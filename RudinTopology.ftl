[set/-s] [element/-s] [subset/-s] [sequence/-s] [number/-s]

Signature NatNum. A natural number is a notion.
Let x, y, z, m, n denote natural numbers.

#### Natural Number Axioms
Signature Addidtion. x + y is a natural number.
Signature Zero. 0 is a natural number. 
Signature One. 1 is a natural number.
Axiom ZeroAddition. x + 0 = x.
Axiom AssAdd. (x + y) + z = x + (y + z).
Axiom ComAdd. x + y = y + x.

Let x is nonzero stand for x != 0.

Axiom OneNotZero.   1 != 0.
Axiom NatPredecessor.      For every nonzero m there exists n such that m = n + 1.

Axiom NonZeroAddition. Let n be a natural number. For all nonzero natural numbers m n + m != 0.

Axiom PredecessorUniq. For all natural numbers n,m if n + 1 = m + 1 then n = m.

Definition Less. x < y iff there exists a nonzero natural number z such that x + z = y.
Lemma SmallestZero. For all nonzero natural numbers x 0 < x.

Lemma Successorgreater. For all natural numbers x x < x + 1.

Lemma Montonicity. Let n,m,x be natural numbers. If n < m then n + x < m + x.
Proof. Assume n < m.
Take a nonzero natural number z such that n + z = m. 
(n + x) + z	.= (n + z) + x (by AssAdd,ComAdd)
		.= m + x.
Then z is a nonzero natural number such that (n + x) + z = m + x.
Then n + x < m + x.
qed.

Lemma MonotonicityOne. Let n,m be natural numbers. If n < m then n + 1 < m + 1.

Lemma AssLess. If x < y and y < z then x < z.
Proof. Assume x < y. Take a nonzero natural number n such that x + n = y. Assume y < z. Take a nonzero natural number m such that y + m = z.
x + (n + m) .= (x + n) + m (by AssAdd)
	    .= y + m
	    .= z.
Then n + m is a nonzero natural number such that x + (n + m) = z (by NonZeroAddition). Then x < z (by Less).
qed.

################## Induction
Signature InbuiltFortheInductionRelation. m -<- n is an atom.
Axiom EmbeddingLessIntoInductionRelation. m < n => m -<- n.

Lemma Trichotomy. For all natural numbers x for all natural numbers y x = y or x < y or y < x.
Proof by induction on x.
Let x be a natural number.
Case x = 0. Let y be a natural number.
	Case y = 0.
	x .= 0
	  .= y.
	end.
	Case y is nonzero.
	x < y (by SmallestZero).
	end.
end.
Case x != 0.
	For all natural numbers a x = a or x < a or a < x.
	Proof by induction on a.
	Let a be a natural number.
		Case a = 0.
		a < x (by SmallestZero).
		end.
		Case a != 0.
		Take m such that m + 1 = x (by NatPredecessor). Then m < x (by Successorgreater).
		Take n such that n + 1 = a (by NatPredecessor). Then n < a (by Successorgreater).
			Case m = n.
			x .= m + 1
			  .= n + 1
			  .= a.
			end.
			Case m < n.
			Then m + 1 < n + 1 (by MonotonicityOne). Then x < a.
			end.
			Case n < m.
			Then n + 1 < m + 1 (by MonotonicityOne). Then a < x.
			end.
		end.
	qed.
end.
qed.

################### Set Theory and Finiteness Notions.
Definition Subset. Let T be a set. A subset of T is a set S such that every element of S is an element of T.

Definition Complement. Let M,N be sets.
M/N = {x in M | x is not an element of N}.

Let S \subset T stand for S is a subset of T. 

Definition ProperSubs. Let T be a set. A proper subset of T is a set S such that S \subset T and there exists an element of T that is not an element of S.

Definition FiniteSet. Let n be a natural number. Fin(n) = { natural number m | m < n}.

Definition Emptyset.
Let S be a set. S is empty iff for all elements x of S Contradiction.

#or alternatively: iff S has no element.

Let S is nonempty stand for S is not empty.

Definition Union. Let S be a set such that every element of S is a set.
\bigcup S = { b | there exists an element T of S such that b is an element of T}.

Definition Intersection. Let S be a set such that every element of S is a set. 
\bigcap S = { b | for all elements T of S b is an element of T}.

Definition surjective. Let T be a set. A Surjection on T is a function f such that for every element t of T there exists an element s of Dom(f) such that f[s] = t.

Let f is surjective on T stand for f is a Surjection on T.

Definition injective.
Let f be a function. f is injective iff for all elements x,y of Dom(f) we have (x!=y => f[x] != f[y]).

Definition Surjection.
Let S, T be sets. 
S ->> T iff there exists a function f such that f is surjective on T and Dom(f) = S.

Definition FinCardinality. 
Let S be a set. Let n be a natural number.
S has cardinality n iff Fin(n) ->> S and for all natural numbers m if m < n then not (Fin(m) ->> S).

Definition SameCardinality.
Let S be a set. Let T be a set. S and T are gleichmaechtig iff there exists a natural number n such that S has cardinality n and T has cardinality n.

Let S ~ T stand for S and T are gleichmaechtig.

Definition Bijection.
Let S,T be sets. 
S <-> T iff there exists a function f such that f is surjective on T and Dom(f) = S and f is injective.

Definition Finiteness. 
Let S be a set. S is finite iff there exists a natural number n such that S has cardinality n.

########### Show that Notion of Cardinality is senseful. Alles Auskommentierte ist nur durch eine Inkonsistenz in den Annahmen wahr gewesen. Ohne diese Inkonsistenz ist der Beweis der Lemmas deutlich aufwändiger und benötigt noch einiges an Vorbereitung, wenn er denn überhaupt ausführbar ist...

Lemma EmptyFinSet. Fin(0) is empty.

#Lemma ProperSubCardinality. Let n be a nonzero natural number. Let S be a set such that S has cardinality n. Let T be a proper subset of S. 
#Let m be a natural number such that T has cardinality m. Then m < n.
#For all natural numbers m if T has cardinality m then m < n.

#Lemma CardIsBijection. Let S be a set. Let n be a natural number such that S has cardinality n. Then Fin(n) <-> S.
#Proof. 

Lemma TildeRefl. Let S be a finite set. Then S ~ S.

Lemma TildeSymm. Let S, T be finite sets. If S ~ T then T ~ S.

Lemma TildeTrans. Let S,T,U be finite sets. If S~T and T~U then S~U.

#Lemma FiniteUnion. Let S be a finite set such that every element of S is finite. Then \bigcup S is finite.

#Lemma IntersectionIsSubset. Let S be a set such that every element of S is a set.
#For all elements T of S \bigcap S \subset T.

#Lemma FiniteSubset. Let S be a set such that S is finite. Let T be a subset of S. T is finite.
#
#Lemma FiniteIntersection. Let S be a finite set such that every element of S is finite. Assume that S is nonempty. Then \bigcap S is finite.
	
############# The Infinite: Sequences, Countability
Definition NAT. NAT = { a | a is a natural number}.

Definition List.
Let S be a set. A list of S is a function f such that Dom(f) = NAT and for every element x of S there exists a natural number n such that f[n] = x.

Definition Ctbl.
Let S be a set.
S is countable iff there exists a function f such that f is a list of S.

Definition Smallest.
Let M be a set. Let N be a subset of M. Let f be a list of M. Let x be an element of N. x is smallest with respect to f and M in N iff there exists a natural number n such that f[n] = x and for every natural number m such that m < n f[m] is not an element of N.

Definition.
Let f be a function such that Dom(f) = NAT. Let n be natural numbers. f << n = {f[m] | m is a natural number and m < n}. 

### Rekursive Funktion. Beweis braucht Existence, Uniqueness, Choices, Well-foundedness.
Proposition. Let M be a set. If M is countable then every subset of M that has an element is countable.
Proof.
Assume M is countable. Take a list f of M. Let N be a subset of M that has an element. Define
			g[n] = 	Case ((M/(f<<n)) has an element) -> Choose an element a of (M/(f<<n)) that is smallest with respect to f and M in (M/(f<<n)) in a, 
				Case ((M/(f<<n)) has no element) -> Choose an element a of N in a
			for n in NAT. 
			proof. Choices. end.
			qed.
