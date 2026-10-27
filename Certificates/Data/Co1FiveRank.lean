module

public import Certificates.Data.TabCo1FiveB
public import CFSG.Sporadic.Co1Block.XFix
public meta import Certificates.Data.TabCo1FiveB
public meta import CFSG.Sporadic.Co1Block.XFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Co1FiveNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.Co1.TwoBNative CFSG.HardMathSupport.Dickson.I271.TabCo1

@[expose] def ext5 : List (List Int) :=
  CFSG.HardMathSupport.Dickson.I271.TabCo1FiveB.ext ++
    [[89, 90], [91, 92, -91], [92, 93], [91, 89, -91]]

@[expose] def betas (f₁ f₂ : Rows) : List Rows :=
  (List.range 25).map fun i => mul (pow f₁ (i / 5)) (pow f₂ (i % 5))

@[expose] def baseA : List Nat :=
  [652327, 4595661, 2713675]

@[expose] def condsA : List (List Cond) :=
  [[([0, 1], []), ([0, 2], []), ([0, 5], []), ([0, 6], []), ([0, 9], []), ([0, 13], [])], [([0,
  1], []), ([0, 2], []), ([0, 5], []), ([0, 6], []), ([0, 7], []), ([0, 8], []), ([0, 9], []),
  ([0, 10], []), ([0, 11], []), ([0, 12], []), ([0, 13], []), ([0, 14], []), ([0], [(0, 0)]),
  ([0, 1], [(0, 0)]), ([0, 5], [(0, 0)]), ([1], [(0, 0)]), ([5], [(0, 0)]), ([0], [(0, 1)]), ([0,
  1], [(0, 1)]), ([0, 5], [(0, 1)]), ([5], [(0, 1)]), ([0], [(0, 2)]), ([0, 1], [(0, 2)]), ([0,
  5], [(0, 2)]), ([5], [(0, 2)]), ([0], [(0, 3)]), ([0, 1], [(0, 3)]), ([0, 5], [(0, 3)]), ([5],
  [(0, 3)]), ([0, 1], [(0, 4)]), ([0, 5], [(0, 4)]), ([1], [(0, 5)]), ([0], [(0, 6)])], [([0, 1],
  []), ([0, 2], []), ([0, 5], []), ([0, 6], []), ([0, 7], []), ([0, 8], []), ([0, 9], []), ([0,
  10], []), ([0, 11], []), ([0, 13], []), ([0, 14], []), ([0], [(0, 0)]), ([0, 1], [(0, 0)]),
  ([1], [(0, 0)]), ([5], [(0, 0)]), ([0], [(0, 1)]), ([0, 1], [(0, 1)]), ([5], [(0, 1)]), ([0],
  [(0, 2)]), ([5], [(0, 2)]), ([0], [(0, 3)]), ([5], [(0, 3)]), ([5], [(0, 4)]), ([0], [(0, 5)]),
  ([0, 1], [(0, 5)]), ([1], [(0, 5)]), ([0], [(0, 6)]), ([0, 1], [(0, 6)]), ([5], [(1, 1)]),
  ([0], [(1, 2)]), ([0, 5], [(1, 2)]), ([0], [(1, 5)])]]

@[expose] def cntsA : List Nat := [50, 5, 1]

@[expose] def spanA : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0), (1, 1), (1, 2), (1,
  3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 15), (2, 0), (2, 5), (2, 10),
  (2, 15)]

@[expose] def combA : List Nat :=
  [13279851, 7155941, 7311238, 15027139, 6287611, 14663760, 6734810, 7920933, 3848565, 15904443,
  7096378, 1729693, 14591485, 3960209, 10971307, 2199879, 13625947, 8383019, 9848192, 13651640,
  12709645, 11198419, 14108910, 8913444]

@[expose] def baseB : List Nat :=
  [10567968, 10800565, 9057456]

@[expose] def condsB : List (List Cond) :=
  [[([0, 1], []), ([0, 2], []), ([0, 5], []), ([0, 6], []), ([0, 7], [])], [([0, 1], []), ([0,
  5], []), ([0, 6], []), ([0, 8], []), ([0, 11], []), ([0, 1], [(0, 0)]), ([0, 1], [(0, 1)])],
  [([0, 1], []), ([0, 2], []), ([0, 5], []), ([0, 6], []), ([0, 7], []), ([0, 8], []), ([0, 10],
  []), ([0, 5], [(0, 0)]), ([0, 5], [(0, 1)]), ([0, 5], [(0, 2)]), ([0], [(1, 0)]), ([1], [(1,
  0)]), ([5], [(1, 0)]), ([0], [(1, 1)]), ([5], [(1, 1)]), ([0], [(1, 2)]), ([5], [(1, 2)]),
  ([0], [(1, 3)]), ([5], [(1, 3)]), ([0, 5], [(1, 4)]), ([5], [(1, 4)]), ([0], [(1, 16)])]]

@[expose] def cntsB : List Nat := [60, 25, 1]

@[expose] def spanB : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (1,
  8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7), (2, 8), (2, 10), (2, 11), (2, 12),
  (2, 13)]

@[expose] def combB : List Nat :=
  [1047553, 1493178, 14328895, 12058665, 14321840, 7904384, 4566959, 301677, 8410065, 2353902,
  7375799, 12906224, 9142949, 8849713, 3057326, 5908947, 14085028, 11445521, 3403202, 12575958,
  6215990, 13327843, 562666, 13361081]

@[expose] def sideOK (t f₁ f₂ f₃ : Rows) (nfix : Nat) (base : List Nat) (conds : List (List Cond))
    (cnts : List Nat) (span : List (Nat × Nat)) (comb : List Nat) : Bool :=
  let FG := [f₁, f₂].toArray
  let Ft := gtBFS FG 100
  let EG := [f₁, f₂, f₃].toArray
  let Et := gtBFS EG 400
  mul t t == one () && CFSG.Sporadic.Co1.InvNative.validRows t && t != one () &&
    CFSG.Sporadic.Co1Block.xFixCount CFSG.Sporadic.Co1Block.certVecs t == nfix &&
    mul t f₁ == mul f₁ t && mul t f₂ == mul f₂ t && mul f₁ f₂ == mul f₂ f₁ &&
    mul f₁ f₃ == mul f₃ f₁ && mul f₂ f₃ == mul f₃ f₂ &&
    gtOK FG Ft && decide (Ft.pts.size = 25) && gtOK EG Et && decide (Et.pts.size = 125) &&
    boundOK (colsOf (betas f₁ f₂)) 25 base conds cnts span comb && decide (cnts.prod ≤ 1999)

@[expose] def co1FiveCheck (_ : Unit := ()) : Bool :=
  let D := kDag ext5
  let kR := nd D 88
  let tR := nd D 91
  let cR := nd D 92
  let c'R := nd D 93
  let dR := nd D 94
  let x₂R := nd D 95
  D.2.2 &&
    sideOK tR kR dR cR 2280 baseA condsA cntsA spanA combA &&
    sideOK x₂R kR cR c'R 0 baseB condsB cntsB spanB combB

end CFSG.LocalAnalysis.GLTheoremA.H1017.Co1FiveNative
