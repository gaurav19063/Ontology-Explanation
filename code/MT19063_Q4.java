package sweb.assignment_sec.que4;
// Importing Required packages
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.coode.owlapi.manchesterowlsyntax.ManchesterOWLSyntaxEditorParser;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.expression.OWLEntityChecker;
import org.semanticweb.owlapi.expression.ShortFormEntityChecker;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.util.BidirectionalShortFormProvider;
import org.semanticweb.owlapi.util.BidirectionalShortFormProviderAdapter;
import org.semanticweb.owlapi.util.ShortFormProvider;
import org.semanticweb.owlapi.util.SimpleShortFormProvider;

import com.clarkparsia.owlapi.explanation.BlackBoxExplanation;
import com.clarkparsia.owlapi.explanation.HSTExplanationGenerator;

import openllet.owlapi.OpenlletReasoner;
import openllet.owlapi.OpenlletReasonerFactory;


public class que4_new {

	// Method to write the text file
	public static void textFileWriting(String s) {
		try {
			String filename = "ReasonarsOutputfile.txt";
			// Open given file in append mode.
			BufferedWriter out = new BufferedWriter(new FileWriter(filename, true));
			out.write(s);
			out.newLine();
			out.close();
		} catch (IOException e) {
			System.out.println("exception occoured" + e);
		}
	}

	// main starts
	public static void main(String[] args) {
		System.out.println("done1");

		try {
			// ontology manager and owldatafactory initialization
			// Map is being used to store all the superclasses for a class

			OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
			OWLDataFactory factory = manager.getOWLDataFactory();
			String ontoname="DSA_04092015.owl";
			OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new File(ontoname));
			textFileWriting("######################################################################");
			textFileWriting("Ontology name: "+ontoname);
			System.out.println("done2");

			Configuration configuration = new Configuration();
			configuration.throwInconsistentOntologyException = false;

			// Hermit Reasoner
			Reasoner hermit = new Reasoner(configuration, ontology);
			System.out.println("Output of Hermit Resoner for ontology consistency: " + hermit.isConsistent());
			System.out.println(hermit.getEquivalentObjectProperties(
					manager.getOWLDataFactory().getOWLObjectProperty(IRI.create("http://example.org/hasBigPart"))));
			// Owl Api Reasoner
			OWLReasoner reasoner = new Reasoner.ReasonerFactory().createReasoner(ontology);
			System.out.println("Output of OWLAPI  Resoner for ontology consistency: " + reasoner.isConsistent());
			// Openllet Reasoner
			OpenlletReasoner oreasoner = (new OpenlletReasonerFactory()).createReasoner(ontology);
			System.out.println("Output of Openllet  Resoner for ontology consistency: " + oreasoner.isConsistent());

			// ---------------------------------------OWL Reasoner Classes Classification
			// ------------------
			Set<String> set_allclasses = new HashSet<String>();
			System.out.println(
					" ############################################ All the classes with subclasses ###################################### ");
			textFileWriting("######################################################################");
			textFileWriting("#############################All the classes with subclasses ###############################");
			for (final OWLSubClassOfAxiom subClasse : ontology.getAxioms(AxiomType.SUBCLASS_OF)) {
				if (subClasse.getSuperClass() instanceof OWLClass && subClasse.getSubClass() instanceof OWLClass) {

					String classString = subClasse.getSubClass().toString();
					if (classString.contains("#")) {
						classString = classString.substring(classString.indexOf("#") + 1, classString.lastIndexOf(">"));
					}
					String superclassString = subClasse.getSuperClass().toString();
					if (superclassString.contains("#")) {
						superclassString = superclassString.substring(superclassString.indexOf("#") + 1,
								superclassString.lastIndexOf(">"));
					}

//	                System.out.println(subClasse.getSubClass() 
//	                     + " extends " + subClasse.getSuperClass());
					String st_temp=classString + " (SubclassOf) " + superclassString;
					textFileWriting(st_temp);
					System.out.println(st_temp);
					set_allclasses.add(classString);
					set_allclasses.add(superclassString);

				}
			}

			System.out.println(" ################################################################################## ");

//	    -------------------------------------------------------------------------------------    
			// Superclasses classification by hermit Reasoner
			// Map is being used to store all the superclasses for a class
			HashMap<String, Set<String>> map_class_superclassses = new HashMap<String, Set<String>>();

			for (String cls : set_allclasses)

			{

				Set<String> temp = new HashSet<String>();

//	        String classExpressionString=cls;

				Set<OWLClass> s;

				if (cls.trim().length() == 0) {
//	            s=Collections.emptySet();
					continue;
				}

				else {
//	        	ShortFormProvider shortFormProvider=new ShortFormProvider ();
					ShortFormProvider shortFormProvider = new SimpleShortFormProvider();
					Query_Processor de = new Query_Processor(hermit, shortFormProvider);
					s = de.getSuperClasses(cls, false);

					for (OWLClass e : s) {
						String cls_name = e.toString();
						if (cls_name.contains("#")) {
							cls_name = cls_name.substring(cls_name.indexOf("#") + 1, cls_name.lastIndexOf(">"));
						}
//		                System.out.println(cls_name.toString());
//		                System.out.println("here");
						temp.add(cls_name);

//		                if(map_class_superclassses.containsKey(cls))
//		                {
//		                	
//		                }
//		                else {
//		                	map_class_superclassses
//		                }

					}

				}

//	        

				map_class_superclassses.put(cls, temp);

			}
			System.out.println(
					" ############################## Superclasses classification by hermit ############################################### ");
			textFileWriting("##############################################################################################");
			textFileWriting("##################### Superclasses classification by hermit:  ###############################");
			for (Map.Entry<String, Set<String>> entry : map_class_superclassses.entrySet()) {
				String stemp = "Class-name (" + entry.getKey() + ")= {";

//				System.out.print(stemp);
				for (String clas : entry.getValue()) {
//					System.out.print(clas + ",");
					stemp += clas + ",";
				}
//				System.out.println('}');
				stemp += '}' ;
				textFileWriting(stemp);

			}
			System.out.println(
					" #################################################################################################################### ");
//-------------------------------------------------------------------------------------------------------------	        
			// Superclasses classification by openllet Reasoner
			// Map is being used to store all the superclasses for a class

			HashMap<String, Set<String>> map_class_superclassses_ = new HashMap<String, Set<String>>();

			for (String cls : set_allclasses)

			{

				Set<String> temp = new HashSet<String>();

//	        String classExpressionString=cls;

				Set<OWLClass> s;

				if (cls.trim().length() == 0) {
//	            s=Collections.emptySet();
					continue;
				}

				else {
//	        	ShortFormProvider shortFormProvider=new ShortFormProvider ();
					ShortFormProvider shortFormProvider = new SimpleShortFormProvider();
					Query_Processor de = new Query_Processor(oreasoner, shortFormProvider);
					s = de.getSuperClasses(cls, false);

					for (OWLClass e : s) {
						String cls_name = e.toString();
						if (cls_name.contains("#")) {
							cls_name = cls_name.substring(cls_name.indexOf("#") + 1, cls_name.lastIndexOf(">"));
						}
//		                System.out.println(cls_name.toString());
//		                System.out.println("here");
						temp.add(cls_name);

//		                if(map_class_superclassses.containsKey(cls))
//		                {
//		                	
//		                }
//		                else {
//		                	map_class_superclassses
//		                }

					}

				}

//	        

				map_class_superclassses_.put(cls, temp);

			}
			textFileWriting("######################################################################################################################");
			textFileWriting("############## Superclasses classification by Openllet:  ########################");
			System.out.println("################# Superclasses classification by Openllet ###################");
			for (Map.Entry<String, Set<String>> entry : map_class_superclassses_.entrySet()) {
				String stemp = "Class-name (" + entry.getKey() + ")= {";
//				System.out.print(stemp);
				for (String clas : entry.getValue()) {
//					System.out.print(clas + ",");
					stemp += clas + ",";
				}
//				System.out.println('}');
				stemp += '}';
				textFileWriting(stemp);
			}

			System.out.println(" ################################################################################## ");
//--------------------------------------------------------------------------------------------------comparision between output of Hermit and openllet-----------------
//	        System.out.println(" There are tripls their class'subclass are different ");
			boolean flag = true;
			for (Map.Entry<String, Set<String>> entry : map_class_superclassses_.entrySet()) {
				Set<String> set_hermit = map_class_superclassses.get(entry.getKey());
				Set<String> set_openlet = map_class_superclassses_.get(entry.getKey());

				if (!set_hermit.containsAll(set_openlet)) {
					// do something if needs be
					System.out.println(entry.getKey());
//					System.out.println("dlkjfasdjfk;sd");
					flag = false;
				}
				if (!set_openlet.containsAll(set_hermit)) {
					flag = false;
					// do something if needs be
				}

//	        	System.out.print("Class-name ("+entry.getKey()+")= {");
//	        	for(String clas: entry.getValue())
//	        	{
//	        		System.out.print(clas+",");
//	        	}
//	        	System.out.println('}');
			}
			if (flag) {
				textFileWriting("######################################################################");
				textFileWriting("Outputs of both the reasoners are same");
				System.out.println("Outputs of both the reasoners are same");
			} else {
				textFileWriting("Outputs of both the reasoners are not same");
				System.out.println("Outputs of both the reasoners are not same");

			}
			System.out.println(" ################################################################################## ");

//	        -----------------------------------------------checking an why ontology inconsistent---------------
			textFileWriting("######################################################################");
			textFileWriting("Explanation of  inconsistent Ontology....");
			// Explanation api use 
			
			OWLDataFactory dataFactory = manager.getOWLDataFactory();
			String st_temp="Stuff.owl";
			ontology = manager.loadOntologyFromOntologyDocument(new File(st_temp));
			textFileWriting("Ontology name for inconsistency:  "+st_temp);
			Reasoner reasoner1 = new Reasoner(configuration, ontology);
//			 OWLReasoner reasoner1=factory.createReasoner(ontology, configuration);
			IRI locationIRI = IRI.create("http://www.iiitd.ac.in/inconsistant/stuff.owl#stuff");

			OWLClass location = dataFactory.getOWLClass(locationIRI);

			



			System.out.println("Inconsistency explanations...");
			textFileWriting("Inconsistency explanations...");
			ReasonerFactory ft = new ReasonerFactory();

			BlackBoxExplanation exp = new BlackBoxExplanation(ontology, ft, reasoner1);
			HSTExplanationGenerator multExplanator = new HSTExplanationGenerator(exp);
//			location dataFactory.getOWLThing())
			Set<Set<OWLAxiom>> explanations = multExplanator.getExplanations(location);
//			Set<Set<OWLAxiom>> explanations = multExplanator.getExplanations(dataFactory.getOWLThing());
//			OWLReasonerFactory rf =new OWLReasonerFactory();
//			ExplanationGeneratorFactory<OWLAxiom> genFac = ExplanationManager.createExplanationGeneratorFactory((OWLReasonerFactory) reasoner1, null);

			// Now create the actual explanation generator for our ontology
//			ExplanationGenerator<OWLAxiom> gen = genFac.createExplanationGenerator(ontology);
//			System.out.println("hello");
			
			for (Set<OWLAxiom> explanation : explanations) {
				System.out.println();
				System.out.println("Axioms causing the Inconsisteccy: ");
				textFileWriting("Axioms causing the Inconsisteccy: ");
				for (OWLAxiom causingAxiom : explanation) {

					System.out.println(causingAxiom);
					textFileWriting(causingAxiom.toString());
				}
				System.out.println();
			}

		}

		catch (OWLOntologyCreationException e) {
			System.out.println("done3");
			e.printStackTrace();

		}
		textFileWriting("######################################################################");
	}
}
//for processing the queries
class Query_Processor {
	private final OWLReasoner reasoner;
	private final parser_query parser;

	public Query_Processor(OWLReasoner reasoner, ShortFormProvider shortFormProvider) {
		this.reasoner = reasoner;
		parser = new parser_query(reasoner.getRootOntology(), shortFormProvider);
	}

	public Set<OWLClass> getSuperClasses(String classExpressionString, boolean direct) {
		if (classExpressionString.trim().length() == 0) {
			return Collections.emptySet();
		}
		OWLClassExpression classExpression = parser.parseClassExpression(classExpressionString);
		NodeSet<OWLClass> superClasses = reasoner.getSuperClasses(classExpression, direct);
		return superClasses.getFlattened();
	}

}
// for parse the queries
class parser_query {

	private final OWLOntology Ontology;
	private final BidirectionalShortFormProvider ShortFormProvider;

	public parser_query(OWLOntology Ontology, ShortFormProvider shortFormProvider) {
		this.Ontology = Ontology;
		OWLOntologyManager manager = Ontology.getOWLOntologyManager();
		Set<OWLOntology> importsClosure = Ontology.getImportsClosure();
		
		ShortFormProvider = new BidirectionalShortFormProviderAdapter(manager, importsClosure, shortFormProvider);
	}

	public OWLClassExpression parseClassExpression(String classExpressionString) {
		OWLDataFactory dataFactory = Ontology.getOWLOntologyManager().getOWLDataFactory();
		ManchesterOWLSyntaxEditorParser parser = new ManchesterOWLSyntaxEditorParser(dataFactory,
				classExpressionString);
		parser.setDefaultOntology(Ontology);
		OWLEntityChecker entityChecker = new ShortFormEntityChecker(ShortFormProvider);
		parser.setOWLEntityChecker(entityChecker);
		return parser.parseClassExpression();
	}
}
