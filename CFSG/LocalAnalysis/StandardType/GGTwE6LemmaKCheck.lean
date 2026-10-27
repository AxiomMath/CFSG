module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6WeylCheck
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbDefs

public section

namespace CFSG.StandardType.TwE6LemmaK

open CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.AGLEmbedding.R3

@[expose] def lemKGens : List (List Nat) := e6SylWords.map e6WordL

@[expose] def lemKDot (a : List Int) (v : List Nat) : Int :=
  (List.zipWith (fun (x : Int) (y : Nat) => x * y) a v).sum

@[expose] def lemKFix (A : List Nat) : List (List Nat) :=
  (allVecs 3 6).filter fun v => matVecA6 A.toArray v == v

@[expose] def lemKTab : List (List Int × List Int × List Nat × List Nat) := [
  ([1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0],
    [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]),
  ([0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1],
    [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1],
    [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 2]),
  ([1, 2, 2, 3, 2, 1], [0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 2, 2, 1, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1])]

@[expose] def lemKCheck (_ : Unit := ()) : Bool :=
  let S := e6SylL ()
  S.length == 81 && decide S.Nodup &&
  S.all (fun A => lemKGens.all fun g => S.contains (mmulL 3 6 A g)) &&
  S.all (fun A => A == midL 3 6 || decide (nfix6 A < 81) ||
      lemKTab.any fun s => A == mmulL 3 6 s.2.2.1 s.2.2.2 || A == mmulL 3 6 s.2.2.2 s.2.2.1) &&
  lemKTab.all fun s => [mmulL 3 6 s.2.2.1 s.2.2.2, mmulL 3 6 s.2.2.2 s.2.2.1].all fun A =>
      (lemKFix A).all fun v => lemKDot s.1 v % 3 == 0 && lemKDot s.2.1 v % 3 == 0

theorem lemKCheck_true : lemKCheck () = true := by decide +kernel

end CFSG.StandardType.TwE6LemmaK
