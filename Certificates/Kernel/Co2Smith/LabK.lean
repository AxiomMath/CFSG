module

public import Certificates.Kernel.Co2Smith.LabData
public import Certificates.Data.Kernel.Co2R3K
public import CFSG.Sporadic.Co2Smith.GlDataWords
public import Certificates.Kernel.Sporadic.Co2.ChainAD
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

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Enum CFSG.KC.Co2R3 CFSG.Sporadic.Co2Rank3.Native CertificateChecks.KernelSpor

@[expose] noncomputable def G0 (k : Nat) : Nat := Co2A.S (level1Idx.getD k (nat_lit 0))

@[expose] noncomputable def G2 (k : Nat) : Nat := Co2A.S (level2Idx.getD k (nat_lit 0))

@[expose] noncomputable def cP : Nat :=
  CFSG.KS.Raw.wordK 2300 12 (CFSG.KS.mask 12) (pidn 2300 12) Co2A.S Co2A.SI
    CFSG.Sporadic.Co2Smith.Native.glCWord

theorem replay0 : orbReplayK 2300 10 G0 (LR 0) (LR 1) (LR 2) (LR 3) (LR 4) (LR 5) = true := by
  decide +kernel

theorem replay1 : orbReplayK 2300 3 WS (LR 6) (LR 7) (LR 8) (LR 9) (LR 10) (LR 11) = true := by
  decide +kernel

theorem replay2 : orbReplayK 2300 8 G2 (LR 12) (LR 13) (LR 14) (LR 15) (LR 16) (LR 17) = true := by
  decide +kernel

theorem ws_ok : ((stabWords ()).length == 3 && (stabWords ()).all
    (CFSG.Monster.B.Co2.Native.lettersOK 11) &&
    allN 3 fun k => Nat.beq (CFSG.KS.Raw.wordK 2300 12 (CFSG.KS.mask 12) (pidn 2300 12) Co2A.S
      Co2A.SI ((stabWords ()).getD k [])) (WS k)) = true := by
  decide +kernel

theorem lab_ok : ([578, 3, 487].all (fun x => Nat.blt (at12 cP x) 2300) &&
    Nat.beq (at12 (LR 6) (at12 cP 578)) 36 && Nat.beq (at12 (LR 6) (at12 cP 3)) 4 &&
    Nat.beq (at12 (LR 6) (at12 cP 487)) 5 && Nat.beq (at12 (LR 12) (at12 cP 3)) 4 &&
    Nat.beq (at12 (LR 0) 2) 1 && Nat.beq (at12 (LR 0) 8) 1) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
