module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Inputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Inputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23C

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native

set_option compiler.extract_closed false

@[expose] def rf (O : WOrbit) (D Bi : Table) (k m : Nat) : Nat :=
  treeAct O.par O.lab O.alpha O.beta D Bi k m

@[expose] def actW (O : WOrbit) (D Bi : Table) (w : List Nat) (m : Nat) : Nat :=
  w.foldr (fun k q => rf O D Bi k q) m

@[expose] def sigEq (O : WOrbit) (D Bi : Table) (u v : List Nat) : Bool :=
  (List.range chainQ.size).all fun t => actW O D Bi u chainQ[t]! == actW O D Bi v chainQ[t]!

@[expose] def twinB (O : WOrbit) (D Bi : Table) (F : List Nat) (a b : Nat) : Bool :=
  a != b && !commB O D Bi a b &&
    F.all fun c => c == a || c == b || (commB O D Bi c a == commB O D Bi c b)

@[expose] def twinPairs (O : WOrbit) (D Bi : Table) (F : List Nat) : List (Nat × Nat) :=
  F.flatMap fun a => (F.filter fun b => twinB O D Bi F a b).map fun b => (a, b)

@[expose] def twinCheck1 (F : List Nat) (P : List (Nat × Nat)) : Bool :=
  F.all fun a => P.any fun p => p.1 == a

@[expose] def twinCheck2 (O : WOrbit) (D Bi : Table) (P : List (Nat × Nat)) : Bool :=
  P.all fun p =>
    rf O D Bi p.1 p.2 != p.1 && rf O D Bi p.1 p.2 != p.2 &&
      P.all fun q => !sigEq O D Bi [p.1, p.2] [q.1, q.2] ||
        q == p || q == (p.2, rf O D Bi p.1 p.2) || q == (rf O D Bi p.1 p.2, p.1)

@[expose] def twinCheck3 (O : WOrbit) (D Bi : Table) (P : List (Nat × Nat)) : Bool :=
  P.all fun p => P.all fun q =>
    sigEq O D Bi [p.1, p.2, q.1, q.2] [q.1, q.2, p.1, p.2]

@[expose] def goodPt (O : WOrbit) (D Bi T : Table) (F : List Nat) (c : Nat) : Bool :=
  decide (c < 31671) && (List.range 31671).all fun c' =>
    !(F.all fun a => commB O D Bi c' a == commB O D Bi c a) ||
      c' == c || c' == ap T c || c' == ap T (ap T c)

@[expose] def twinCheck4 (O : WOrbit) (D Bi T : Table) (F : List Nat) (k : Nat) : Bool :=
  (List.range chainQ.size).all fun t => goodPt O D Bi T F (rf O D Bi k chainQ[t]!)

@[expose] def twinCheck (O : WOrbit) (D Bi T : Table) (k : Nat) : Bool :=
  let F := fixList T
  let P := twinPairs O D Bi F
  twinCheck1 F P && twinCheck2 O D Bi P && twinCheck3 O D Bi P && twinCheck4 O D Bi T F k

@[expose] def fi23COK (O : WOrbit) : Bool :=
  let T := t3Tabs O (chainLetters O)
  twinCheck O (dTable O) (genTables O (-2)) T[2]! 4

end CFSG.HardMathSupport.Dickson.I271.TabFi23C
