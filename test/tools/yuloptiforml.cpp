/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0
/**
 * Interactive yul optimizer
 */

#include <libsolutil/CommonIO.h>
#include <libsolutil/Exceptions.h>
#include <libsolutil/StringUtils.h>
#include <liblangutil/ErrorReporter.h>
#include <libyul/AsmAnalysis.h>
#include <libyul/AsmAnalysisInfo.h>
#include <libsolidity/parsing/Parser.h>
#include <libyul/AST.h>
#include <libyul/AsmParser.h>
#include <libyul/ObjectParser.h>
#include <libyul/Object.h>
#include <liblangutil/SourceReferenceFormatter.h>

#include <libyul/optimiser/Disambiguator.h>
#include <libyul/optimiser/OptimiserStep.h>
#include <libyul/optimiser/Suite.h>

#include <libyul/backends/evm/EVMDialect.h>

#include <libsolutil/JSON.h>

#include <libsolidity/interface/OptimiserSettings.h>
#include <liblangutil/CharStreamProvider.h>

#include <boost/algorithm/string/predicate.hpp>
#include <boost/algorithm/string/join.hpp>
#include <boost/program_options.hpp>

#include <range/v3/action/sort.hpp>
#include <range/v3/range/conversion.hpp>
#include <range/v3/view/concat.hpp>
#include <range/v3/view/drop.hpp>
#include <range/v3/view/map.hpp>
#include <range/v3/view/set_algorithm.hpp>
#include <range/v3/view/stride.hpp>
#include <range/v3/view/transform.hpp>

#include <string>
#include <iostream>
#include <variant>

using namespace solidity;
using namespace solidity::util;
using namespace solidity::langutil;
using namespace solidity::frontend;
using namespace solidity::yul;

namespace po = boost::program_options;

class YulOpti
{
public:
	static void printErrors(CharStream const& _charStream, ErrorList const& _errors)
	{
		SourceReferenceFormatter{
			std::cerr,
			SingletonCharStreamProvider(_charStream),
			true,
			false
		}.printErrorInformation(_errors);
	}

	void parse(std::string const& _input, std::string const& _name = "")
	{
		ErrorList errors;
		ErrorReporter errorReporter(errors);
		//std::string source = print(nullptr /* _soliditySourceProvider */);
		m_charStream = std::make_unique<CharStream>(_input, _name);
		try
		{
			std::shared_ptr<Scanner> scanner = std::make_shared<Scanner>(*m_charStream);
			auto rootObj = yul::ObjectParser(errorReporter, m_dialect).parse(scanner, false);
			if (!rootObj || errorReporter.hasErrors())
			{
				std::cerr << "Error parsing source." << std::endl;
				printErrors(*m_charStream, errors);
				throw std::runtime_error("Could not parse source.");
			}
			m_rootObj = rootObj;
			if (!analyzeParsed(*m_rootObj, errorReporter)) {
				std::cerr << "Error while analysing source." << std::endl;
				printErrors(*m_charStream, errors);
				throw std::runtime_error("Could not analyse source.");
			}
		}
		catch(...)
		{
			std::cerr << "Fatal error during parsing: " << std::endl;
			printErrors(*m_charStream, errors);
			throw;
		}
	}

	bool analyzeParsed(Object& _object, ErrorReporter& errorReporter) {
		_object.analysisInfo = std::make_shared<AsmAnalysisInfo>();

		AsmAnalyzer analyzer(
			*_object.analysisInfo,
			errorReporter,
			m_dialect,
			{},
			_object.qualifiedDataNames()
		);

		bool success = false;
		try
		{
			success = analyzer.analyze(_object.code()->root());
			for (auto& subNode: _object.subObjects)
				if (auto subObject = dynamic_cast<Object*>(subNode.get()))
					if (!analyzeParsed(*subObject, errorReporter))
						success = false;
		}
		catch (UnimplementedFeatureError const& _error)
		{
			errorReporter.unimplementedFeatureError(1920_error, _error.sourceLocation(), *_error.comment());
			success = false;
		}

		return success;
	}

	void printUsageBanner(
		std::map<char, std::string> const& _extraOptions,
		size_t _columns
	)
	{
		yulAssert(_columns > 0);
		auto const& optimiserSteps = OptimiserSuite::stepAbbreviationToNameMap();
		auto hasShorterString = [](auto const& a, auto const& b) { return a.second.size() < b.second.size(); };
		size_t longestDescriptionLength = std::max(
			max_element(optimiserSteps.begin(), optimiserSteps.end(), hasShorterString)->second.size(),
			max_element(_extraOptions.begin(), _extraOptions.end(), hasShorterString)->second.size()
		);

		std::vector<std::string> overlappingAbbreviations =
			ranges::views::set_intersection(_extraOptions | ranges::views::keys, optimiserSteps | ranges::views::keys) |
			ranges::views::transform([](char _abbreviation){ return std::string(1, _abbreviation); }) |
			ranges::to<std::vector>();

		yulAssert(
			overlappingAbbreviations.empty(),
			"ERROR: Conflict between yulopti controls and the following Yul optimizer step abbreviations: " +
			boost::join(overlappingAbbreviations, ", ") + ".\n"
			"This is most likely caused by someone adding a new step abbreviation to "
			"OptimiserSuite::stepNameToAbbreviationMap() and not realizing that it's used by yulopti.\n"
			"Please update the code to use a different character and recompile yulopti."
		);

		std::vector<std::tuple<char, std::string>> sortedOptions =
			ranges::views::concat(optimiserSteps, _extraOptions) |
			ranges::to<std::vector<std::tuple<char, std::string>>>() |
			ranges::actions::sort([](std::tuple<char, std::string> const& _a, std::tuple<char, std::string> const& _b) {
				return (
					!boost::algorithm::iequals(get<1>(_a), get<1>(_b)) ?
					boost::algorithm::lexicographical_compare(get<1>(_a), get<1>(_b), boost::algorithm::is_iless()) :
					toLower(get<0>(_a)) < toLower(get<0>(_b))
				);
			});

		yulAssert(sortedOptions.size() > 0);
		size_t rows = (sortedOptions.size() - 1) / _columns + 1;
		for (size_t row = 0; row < rows; ++row)
		{
			for (auto const& [key, name]: sortedOptions | ranges::views::drop(row) | ranges::views::stride(rows))
				std::cout << key << ": " << std::setw(static_cast<int>(longestDescriptionLength)) << std::setiosflags(std::ios::left) << name << " ";

			std::cout << std::endl;
		}
	}

	yul::Block disambiguate(const yul::Object& yulObj)
	{
		auto astRoot = std::get<yul::Block>(Disambiguator(m_dialect, *yulObj.analysisInfo)(yulObj.code()->root()));
		m_nameDispenser.reset(astRoot);

		return astRoot;
	}

	void begin(std::string _source) {
		parse(_source);
		runSteps(*m_rootObj, "hgfo", false);

		parse(m_rootObj->toString(), m_charStream->name()); // reparse
		std::cout << m_rootObj->toString();
	}

	void end(std::string _source) {
		parse(_source);
		runSteps(*m_rootObj, "g", false);
		parse(m_rootObj->toString(), m_charStream->name()); // reparse
		std::cout << m_rootObj->toString();
	}

	void steps(std::string _source, std::string _steps) {
		parse(_source);
		runSteps(*m_rootObj, _steps, false);
		parse(m_rootObj->toString(), m_charStream->name()); // reparse
		std::cout << m_rootObj->toString();
	}

	void toJson(std::string _source) {
		parse(_source);
		std::cout << m_rootObj->toJson();
	}

	void runSteps(yul::Object& _object, std::string _steps, bool _isCreation)
	{
		for (auto& subNode: _object.subObjects)
			if (auto subObject = dynamic_cast<Object*>(subNode.get()))
			{
				bool isCreation = !boost::ends_with(subObject->name, "_deployed");
				runSteps(*subObject, _steps, isCreation);
			}

		auto astRoot = disambiguate(_object);
		OptimiserStepContext context{
			m_dialect,
			m_nameDispenser,
			m_reservedIdentifiers,
			_isCreation ? std::nullopt : std::make_optional(solidity::frontend::OptimiserSettings::standard().expectedExecutionsPerDeployment)
		};
		OptimiserSuite{context}.runSequence(_steps, astRoot);
		_object.setCode(std::make_shared<AST>(std::move(astRoot)));
		_object.analysisInfo = std::make_shared<AsmAnalysisInfo>(AsmAnalyzer::analyzeStrictAssertCorrect(m_dialect, _object));
	}

private:
	std::shared_ptr<yul::Object> m_rootObj;
	std::unique_ptr<langutil::CharStream> m_charStream;
	Dialect const& m_dialect{EVMDialect::strictAssemblyForEVMObjects(EVMVersion{})};
	std::unique_ptr<AsmAnalysisInfo> m_analysisInfo;
	std::set<YulName> const m_reservedIdentifiers = {};
	NameDispenser m_nameDispenser{m_dialect, m_reservedIdentifiers};
	OptimiserStepContext m_context{
		m_dialect,
		m_nameDispenser,
		m_reservedIdentifiers,
		solidity::frontend::OptimiserSettings::standard().expectedExecutionsPerDeployment
	};
};

int main(int argc, char** argv)
{
	try
	{
		po::options_description options(
			R"(yuloptiforml, yul optimizer exploration tool.
	Usage: yuloptiforml [Options] <file>
	Reads <file> as yul code and applies optimizer steps to it,
	interactively read from stdin.
	In non-interactive mode a list of steps has to be provided.
	If <file> is -, yul code is read from stdin and run non-interactively.

	Allowed options)",
			po::options_description::m_default_line_length,
			po::options_description::m_default_line_length - 23);
		options.add_options()
			(
				"input-file",
				po::value<std::string>(),
				"input file"
			)(
				"steps",
				po::value<std::string>(),
				"steps to execute non-interactively"
			)(
				"begin",
				"init steps to execute non-interactively"
			)(
				"end",
				"final steps to execute non-interactively"
			)(
				"json",
				"print json representation of the contract"
			)("help,h", "Show this help screen.");

		// All positional options should be interpreted as input files
		po::positional_options_description filesPositions;
		filesPositions.add("input-file", 1);

		po::variables_map arguments;
		po::command_line_parser cmdLineParser(argc, argv);
		cmdLineParser.options(options).positional(filesPositions);
		po::store(cmdLineParser.run(), arguments);
		po::notify(arguments);

		if (arguments.count("help"))
		{
			std::cout << options;
			return 0;
		}

		std::string input;
		if (arguments.count("input-file"))
		{
			std::string filename = arguments["input-file"].as<std::string>();
			if (filename == "-")
			{
				input = readUntilEnd(std::cin);
			}
			else
				input = readFileAsString(arguments["input-file"].as<std::string>());
		}
		else
		{
			std::cout << options;
			return 1;
		}

		YulOpti yulOpti;
		if (arguments.count("steps"))
		{
			std::string sequence = arguments["steps"].as<std::string>();
			yulOpti.steps(input, sequence);
		}
		if (arguments.count("begin"))
		{
			yulOpti.begin(input);
		}
		if (arguments.count("end"))
		{
			yulOpti.end(input);
		}
		if (arguments.count("json"))
		{
			yulOpti.toJson(input);
		}

		return 0;
	}
	catch (po::error const& _exception)
	{
		std::cerr << _exception.what() << std::endl;
		return 1;
	}
	catch (FileNotFound const& _exception)
	{
		std::cerr << "File not found:" << _exception.comment() << std::endl;
		return 1;
	}
	catch (NotAFile const& _exception)
	{
		std::cerr << "Not a regular file:" << _exception.comment() << std::endl;
		return 1;
	}
	catch(...)
	{
		std::cerr << std::endl << "Exception:" << std::endl;
		std::cerr << boost::current_exception_diagnostic_information() << std::endl;
		return 1;
	}
}
