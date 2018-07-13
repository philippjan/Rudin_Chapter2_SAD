[openset/-s] [topology/topologies] [set/sets] [covering/-s] [collection/-s]

##### Intersection ### \cap ist Schnitt von zwei offenen Mengen ### \cap1 is schnitt von offener Menge mit Menge
Let S1,S2 denote sets.
Signature. S1 \cap S2 is a set.
#Signature. Let S be a set. Let O be an open set. 
#O \cap1 S is a set and open in S.

##### Union
Signature. S1 \cup S2 is a set.
#Signature. Let C be a collection. \bigcup(C) is an open set.


##### Subset  ##### Wegen starker Axiome reicht das so.  
Definition DefSub. A subset of S is a set.

Let A [= B stand for A is a subset of B.

### Open set ist offene Menge im "Universum". Open set of S ist open set in subtopology
Signature Openset. 	Let A be a set. A is open is an atom.
#Signature Subtopology. A subtopology is a notion.
Signature OpensetOfSet.	Let S be a set. Let A [= S. A is open in S is an atom. 

####### subspaces are sets
Let S denote a set.

### We only know the subtopology. So if we ask for open sets in a subspace S we've already assume that these S is equipped with the subspacetopology.
###
Definition SubtopOfSubsp.
Let S be a set.
The subtopology on S is a set T such that for every element y of T (T is a set and T is open in S).

Let O,O1,O2 denote open sets.

Definition Collection. A collection is a set C such that every element of C is a set. 
Let C denote a collection.

Signature CollectOf. Let S be a set. A collection of S is a collection.

########### Finite collection
Signature FiniteColle.	Let C be a collection. C is finite is an atom.



#### Subspace Relation. Die Relation drückt aus, dass S von D überdeckt wird.
Signature. Assume D is a collection. Let S be a set. D covers S is an atom.

#Axiom SubtopOpensets. Let S be a set. Let O [= S. Let O be open in S.
#Then there exists an open set O1 such that (O1 \cap1 S) = O.

Signature CollecInter.	Let C be a collection. Let S be a set. 
C \capcap S is a collection of S.

### Embed soll eine Auswahl von offenen Mengen V_i sein, sodass (V_i \cap S) in D ist.
Signature CollecEmbed. 	Let S be a set. Let D be a collection of S. 
\embed(D,S) is a collection.

###### Wahrscheinlich unnötig. Ich muss alles auf der Covering ebene machen. Der Prover kann nicht selbstständig rausfinden, ob eine Collection ein Covering ist. Das ist sehr mühselig und benötigt Mengentheorie.
#Axiom Inverse.
#	Let S be a set. Let D be a collection of S. \embed(D) \capcap S = D.
#
#Axiom Included.
#	Let D be a collection. Let S be a set. \embed(D \capcap S) [= D.

####### Finiteness ist eine atomare Aussage ohne Inhalt. Deshalb kann ich dieses Prädikat nur axiomatisch weitergeben. Endlichkeit als abgeleiteten Begriff aufzufassen erscheint mir sehr kompliziert. 

Axiom FinCollect1.	Assume C is a finite collection. Let S be a set. Let E [= S. Let C covers E. Then there exists a collection C0 such that (C0 is a collection of S and C0 covers E).

Axiom Fincollect2.	Assume S is a set. Let E [= S. Let C be a finite collection of S such that C covers E. There exists a finite collection C0 such that C0 covers E.

###### Cover ####
## Subcoverings müssen nicht als Teilmenge von Coverings spezifiziert werden, da wir im Theorem so oder so nur ihre Existenz behaupten, ohne intrinsische Eigenschaften zu nutzen. Würde man es dennoch tun, müsste man noch zusätzlich die Vererbarkeit dieser Teilmengen Eigenschaft bzgl. \capcap erklären. Die entscheidenden Deduktionsschritte sind axiomatisch zwischen Coverings definiert. Deshalb ließe sich der Beweis eventuell auch noch verkürzen, indem man sich nur auf Coverings konzentriert.

Definition Covering.
Let S be a set. A covering of S is a collection D such that D covers S and every element of D is open.

Definition Subcovering.
Let S be a set. Let D be a covering of S. A subcovering of S and D is a covering of S.

Definition CoveringIn.
Let S be a set. Let U [= S. A covering of U in S is a collection D such that D is a collection of S and D covers U and every element of D is open in S.

Definition SubcoveringIn.
Let S be a set. Let U [= S. Let D be a covering of U in S. A subcovering of U and D in S is a covering of U in S.

#######Diese konstanten Terme bekommen die strukturellen Eigenschaften der Mengen
#{A\cap S | A \in T0} bzw. {A | A \cap S \in T1}.

Axiom. Let S be a set. Let K [= S. Let D be a covering of K. 
Then D \capcap S is a covering of K in S.

Axiom. Let S be a set. Let K [= S. Let D be covering of K in S. 
Then \embed(D,S) is a covering of K.

###### Vererbbarkeit der Endlichkeit von coverings. 
Axiom FinCover1.	Let  S be a set. Let E [= S. Assume D is a finite covering of E. Then D \capcap S is a finite covering of E in S.

Axiom FinCover2.	Let S be a set. Let E [= S. Assume D is a finite covering of E in S. Then \embed(D,S) is a finite covering of E.

####### Compactness

#Signature Compactness.	Let K be a set. K is compact is an atom. 
#Signature CompactInSet.	Let S be a set. Let K [= S. K is compact in S is an atom.

Definition Compactness. 
Let K be a set.
K is compact iff for every collection D ((D is a covering of K) => (there exists a finite subcovering of K and D)).  

Definition CompactInSetax.	
Let S be a set. Let K [= S.
K is compact in S iff for every collection D ((D is a covering of K in S) => (there exists a finite subcovering of K and D in S)).

Theorem Compactsubs. Let S be a set. Let K [= S.
Then K is compact iff K is compact in S.
Proof.
Let us show that (K is compact) => (K is compact in S).
	Assume K is compact. Assume D0 is a covering of K in S. 
	Take a collection D1 such that D1 is a finite subcovering of K and \embed(D0,S). 
	Then D1 \capcap S is a finite subcovering of K and D0 in S.
	Then K is compact in S.
End.
Let us show that (K is compact in S) => (K is compact).
	Assume K is compact in S. Assume D0 is a covering of K. 
	Take a collection D1 such that D1 is a finite subcovering of K and (D0 \capcap S) in S. 
	Then \embed(D1, S) is a finite subcovering of K and D0.
	Then K is compact.
End.
qed.
##### Compactness ist darüberhinaus etwas witzlos finde ich, da sich die Endlichkeit nur axiomatisch herstellen lässt.
