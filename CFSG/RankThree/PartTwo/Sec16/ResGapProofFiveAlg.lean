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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec16.ResGapFive.Alg

variable {W : Type*} [AddCommGroup W]

theorem norm_five_eq_zero (X : W →+ W) (hX5 : ∀ w, X (X (X (X (X w)))) = w)
    (hXf : ∀ w, X w = w → w = 0) (w : W) :
    w + X w + X (X w) + X (X (X w)) + X (X (X (X w))) = 0 := by
  apply hXf
  simp only [map_add, hX5]
  abel

theorem norm_three_eq_zero (C : W →+ W) (hC3 : ∀ w, C (C (C w)) = w)
    (hCf : ∀ w, C w = w → w = 0) (w : W) :
    w + C w + C (C w) = 0 := by
  apply hCf
  simp only [map_add, hC3]
  abel

theorem key_identity (h2 : ∀ w : W, w + w = 0) (X C : W →+ W)
    (hX5 : ∀ w, X (X (X (X (X w)))) = w) (hXC : ∀ w, X (C w) = C (X w))
    (hN5 : ∀ w, w + X w + X (X w) + X (X (X w)) + X (X (X (X w))) = 0)
    (hN3 : ∀ w, w + C w + C (C w) = 0) (w : W) :
    C (C w - (X (X w) + X (X (X w)))) -
        (X (C w - (X (X w) + X (X (X w)))) +
          X (X (X (X (C w - (X (X w) + X (X (X w)))))))) = 0 := by
  have n1 := hN5 w
  have n2 : C w + C (X w) + C (X (X w)) + C (X (X (X w))) + C (X (X (X (X w)))) = 0 := by
    have := congrArg C (hN5 w)
    simpa only [map_add, map_zero] using this
  have n3 := hN3 w
  have t := h2 w
  simp only [map_sub, map_add, hXC, hX5]
  calc C (C w) - (C (X (X w)) + C (X (X (X w)))) -
        (C (X w) - (X (X (X w)) + X (X (X (X w)))) +
          (C (X (X (X (X w)))) - (X w + X (X w))))
      = (w + C w + C (C w)) -
          (C w + C (X w) + C (X (X w)) + C (X (X (X w))) + C (X (X (X (X w))))) +
          (w + X w + X (X w) + X (X (X w)) + X (X (X (X w)))) - (w + w) := by abel
    _ = 0 := by rw [n1, n2, n3, t]; abel

theorem eq_omega_or (h2 : ∀ w : W, w + w = 0) (X C : W →+ W)
    (hX5 : ∀ w, X (X (X (X (X w)))) = w) (hC3 : ∀ w, C (C (C w)) = w)
    (hXC : ∀ w, X (C w) = C (X w)) (hXf : ∀ w, X w = w → w = 0)
    (hCf : ∀ w, C w = w → w = 0)
    (hirr : ∀ V : AddSubgroup W, (∀ v ∈ V, X v ∈ V) → (∀ v ∈ V, C v ∈ V) → V = ⊥ ∨ V = ⊤) :
    (∀ w, C w = X w + X (X (X (X w)))) ∨ (∀ w, C w = X (X w) + X (X (X w))) := by
  have hN5 := norm_five_eq_zero X hX5 hXf
  have hN3 := norm_three_eq_zero C hC3 hCf
  set V : AddSubgroup W :=
    { carrier := {v | C v = X v + X (X (X (X v)))}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        rw [ha, hb]
        abel
      zero_mem' := by simp
      neg_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq, map_neg] at ha ⊢
        rw [ha]
        abel } with hV
  have hVX : ∀ v ∈ V, X v ∈ V := by
    intro v hv
    change C v = X v + X (X (X (X v))) at hv
    change C (X v) = X (X v) + X (X (X (X (X v))))
    rw [← hXC, hv, map_add]
  have hVC : ∀ v ∈ V, C v ∈ V := by
    intro v hv
    change C v = X v + X (X (X (X v))) at hv
    change C (C v) = X (C v) + X (X (X (X (C v))))
    simp only [hXC]
    rw [← map_add, ← hv]
  rcases hirr V hVX hVC with hbot | htop
  · right
    intro w
    set g := C w - (X (X w) + X (X (X w))) with hg
    have hgV : g ∈ V := by
      change C g = X g + X (X (X (X g)))
      have := key_identity h2 X C hX5 hXC hN5 hN3 w
      rw [← hg] at this
      exact sub_eq_zero.mp this
    rw [hbot, AddSubgroup.mem_bot] at hgV
    exact sub_eq_zero.mp hgV
  · left
    intro w
    exact (htop ▸ AddSubgroup.mem_top w : w ∈ V)

end CFSG.RankThree.PartTwo.Sec16.ResGapFive.Alg
