module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Inputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Inputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23Y

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native

set_option compiler.extract_closed false

@[expose] def yEdgesD : List (Nat × Nat) := [(0, 1), (0, 4), (0, 6), (1, 2), (2, 3), (4, 5), (6, 7)]

@[expose] def pairWordD (s t : Nat) : List Nat :=
  (List.replicate (if (s, t) ∈ yEdgesD then 3 else 2) [s, t]).flatten

@[expose] def yRelsD : List (List Nat) :=
  (List.range 8).map (fun s => [s, s]) ++
    ((List.range 8).flatMap fun s => ((List.range 8).filter (s < ·)).map fun t => pairWordD s t) ++
    [(List.replicate 10 [0, 1, 2, 0, 4, 5, 0, 6, 7]).flatten]

@[expose] def y322Ks : List Nat := [31036, 4160, 24410, 2219, 10570, 10625, 8783, 21988]

@[expose] def yCheck (O : WOrbit) (D Bi T : Table) (ks : List Nat) : Bool :=
  ks.length == 8 && ks.all (· < 31671) && ks.all (fun k => ap T k == k) &&
    yRelsD.all (fun w => w.all (· < 8)) &&
    yRelsD.all (fun w => eqTab (starWordTab O D Bi (w.map fun c => ks[c]!)) (idT 31671)) &&
    !eqTab (starWordTab O D Bi [ks[0]!, ks[1]!]) (starWordTab O D Bi [ks[1]!, ks[0]!])

@[expose] def fi23YOK (O : WOrbit) : Bool :=
  yCheck O (dTable O) (genTables O (-2)) (t3Tabs O (chainLetters O))[0]! y322Ks

end CFSG.HardMathSupport.Dickson.I271.TabFi23Y
