module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Timmesfeld.Moufang.SigmaFar.DataK24

@[expose] noncomputable def edgeBlk0 : ℕ := 0xb8a5e4212f4177abdd3eca368f7cb4559c2d60ea89564e72b2156aad5366a945364a523162730b945ae494a524a885284532318980630412a1049407bc21d1088e3a7391da0e70d346b618c98c462a5ad14914a84204a4106908431439e0840c6022818c1430a5810a211041063800210900002100
@[expose] noncomputable def edgeBlk (_b : ℕ) : ℕ :=
  edgeBlk0
@[expose] noncomputable def edge (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (edgeBlk (Nat.shiftRight i 11))
    (Nat.mul 13 (Nat.land i 2047))) 8191
@[expose] noncomputable def fx (f : ℕ) : ℕ :=
  Nat.land (edge f) 31
@[expose] noncomputable def fc (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (edge f) 5) 7
@[expose] noncomputable def fy (f : ℕ) : ℕ :=
  Nat.shiftRight (edge f) 8

@[expose] noncomputable def justBlk0 : ℕ := 0xacb99d55710a7de354bbc5695788c0000022ad4d4458428470ccf8e189e9c2500000076a99ce95109b9a2931b45e61688c0000017e6232a529a526084000001416250000004e908490a14919423000000448894809138f92210000003c8094689158c9223000000304094000000b9c21141c5226388c00000091a2510184e1e308400000070c230000001a288c0000006082100000016209400000050623000000121084000000404250000000e28941411382022100000006088c0000001002100000002008c00000000025000000
@[expose] noncomputable def justBlk (_b : ℕ) : ℕ :=
  justBlk0
@[expose] noncomputable def just (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (justBlk (Nat.shiftRight i 11))
    (Nat.mul 23 (Nat.land i 2047))) 8388607
@[expose] noncomputable def kind (f : ℕ) : ℕ := Nat.land (just f) 3
@[expose] noncomputable def wi (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 2) 15
@[expose] noncomputable def ft (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 6) 15
@[expose] noncomputable def fs (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 10) 31
@[expose] noncomputable def fo (f : ℕ) : ℕ :=
  Nat.shiftRight (just f) 15

@[expose] noncomputable def refsBlk0 : ℕ := 0x644c8a008a4420141608061a324c00844420142e626a0084008400565a70765e2c1622467e007e424600783c386e76585400780078005e6272007234326668006c3a3834324c48242a5a006c006c006800602c1614100e264a4e6600640060005c280c122e005800580054242a00500050004c240c00061a3200480048004400401c040a22003c003c0038181e003400340030002c002800240020001c00180014000a00100010000c000800040000
@[expose] noncomputable def refsBlk (_b : ℕ) : ℕ :=
  refsBlk0
@[expose] noncomputable def refs (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (refsBlk (Nat.shiftRight i 11))
    (Nat.mul 8 (Nat.land i 2047))) 255
@[expose] noncomputable def plBlk0 : ℕ := 0x6b625d584d48434138332e2c25201c17120e0b0904020000
@[expose] noncomputable def plBlk (_b : ℕ) : ℕ :=
  plBlk0
@[expose] noncomputable def pl (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (plBlk (Nat.shiftRight i 11))
    (Nat.mul 8 (Nat.land i 2047))) 255
@[expose] noncomputable def ffiBlk0 : ℕ := 0x8d8a85868f88817e837c797a75726d6e77706566696a898e73746b6861625f5c595a717651527d8257548b8c494a4f4c7f808784454643403d3e7b7835366f6c3b38676431324d4e5d5e2d2e6360292a5b58555653504b4825264142212247441d1e3f3c393a37343330191a11122f2c17142b280d0e2724090a232015161f1c05061b1813100f0c01020b0807040300
@[expose] noncomputable def ffiBlk (_b : ℕ) : ℕ :=
  ffiBlk0
@[expose] noncomputable def ffi (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (ffiBlk (Nat.shiftRight i 11))
    (Nat.mul 8 (Nat.land i 2047))) 255
@[expose] noncomputable def liveMask : ℕ := 0xffffff
@[expose] noncomputable def live (x : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight liveMask x) 1) 1

@[expose] noncomputable def words : List (List ℕ) :=
  [[4, 4], [2, 2], [0, 0], [4, 0, 4, 0], [2, 4, 2, 4, 2, 4], [2, 0, 2, 0, 2, 0, 2, 0], [4, 0, 2,
    0, 2, 4, 0, 0, 2, 0, 2], [2, 0, 2, 4, 0, 2, 0, 2, 4, 0, 0], [0, 2, 0, 2, 0, 2, 0, 2], [0, 4,
    0, 4], [2, 4, 0, 2, 0, 2, 4, 0, 0, 2, 0]]

@[expose] noncomputable def subs : List (List ℕ) :=
  []

end CFSG.Timmesfeld.Moufang.SigmaFar.DataK24
