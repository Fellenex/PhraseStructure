open util/boolean 

/*
X' Phrase Theory Formal Specification
(Dependent on left-headed languages)
Written by Chris Keeler, November 5th, 2014 -> November 20th, 2014
*/

abstract sig Node{
	parent : lone Node,
	leftChild : lone Node,
	rightChild : lone Node
/*
	Dummy class.
	Needed because X' developments use the following (possibly) recursive productions
	
		X' := X0 | X0 . Complement | X' . Adjunct
*/
}

sig Root extends Node{
	mainPhrase : one XP
}

sig XP extends Node{
// L-R lone spec/ one X'
	isRoot : Bool
}

sig XPrime extends Node{
	transitive : False
}

sig Head extends Node{
	content : String
}

sig Specifier extends Node{
}

//XPs which complement the head of the current XP
sig Complement extends Node{
}

sig Adjunct extends Node{
	content : String
}

fact rootDifferences{
	//Doesn't break any of the properties of Node, because they all require "lone" parent/leftChild/rightChild
	no Root.parent
	no Root.leftChild
	no Root.rightChild

	//The main phrase (XP) of any tree should point to the root as its parent
	all r : Root | r.mainPhrase.parent = r

	all xp : XP | !(xp.parent in Root) => xp.isRoot.isFalse
	all xp : XP | xp.parent in Root => xp.isRoot.isTrue
}

fact nodeRules{
	//All non-root nodes are in at least one tree.
	(Node-Root) in (Root.mainPhrase.*(leftChild + rightChild)) 
}

fact parentRules{
	//All nodes (except roots) have one parent
	all n : Node-Root | one p : Node | n.parent=p

	//Any children of a node, n, should point to n as a parent
	all n : Node | one n.leftChild => (n.leftChild.parent = n)
	all n : Node | one n.rightChild => (n.rightChild.parent = n)
}

fact childrenRules{
	//an XP's children are 0 or 1 Specifiers on the left, and 1 X' on the right.
	all xp : XP | lone s : Specifier | s in xp.leftChild

	//Only X's occur as the right child of XP.
	//This means the set of all XP's right children minus the set of all X' should be the null set)
	(XP.rightChild-XPrime)=none

	//Only Specifiers occur as the left child of XP.
	//This means the set of all XP's left children minus the set of all Specifiers should be the null set)
	(XP.leftChild-Specifier)=none

	all xp : XP | one x : XPrime | x in xp.rightChild

	//Heads, adjuncts, and specifiers do not have any children
	no Specifier.leftChild && no Specifier.rightChild
	no Adjunct.leftChild && no Adjunct.rightChild
	no Head.leftChild && no Head.rightChild

	//Complements do not have any children (For now)
	no Complement.leftChild && no Complement.rightChild

	//Nodes cannot have both of their children be the same value
	no (Node.leftChild & Node.rightChild)
}

fact lineageRules{
	//No nodes have themselves in their ancestry
	no n : Node | n in n.^parent

	//No nodes have themselves in their children's lineage
	no n : Node | n in n.^(leftChild+rightChild)

	//The set of ancestors and children are disjoint
	//That is to say, any parent of one node cannot appear
	no (Node.parent & Node.(leftChild+rightChild))
}

fact xPrimeRules{
	//Intransitive X' have one head, and zero complements
//	all i : XPrime | i.transitive.isFalse => (one h : Head | lone c : Complement | (i.leftChild = h) && (i.rightChild = c))
//	all i : XPrime | i.transitive.isFalse => (i.leftChild in Head) && (i.rightChild=none)

	//Transitive X' have one head, and one complement.


	//Recursive X' have leftChild==X', and rightChild=Adjunct
//	all t : XPrime | t.transitive.isTrue => (one x : XPrime | one a : Adjunct | (t.leftChild = x)  && (t.rightChild = a))


}

//All the nodes from a root
fun nodes[r : Root] : set Node {
	(r.mainPhrase).*(leftChild + rightChild)
}

pred Show{
	one Root
}

run Show for 4
//check childrenRules for 4
