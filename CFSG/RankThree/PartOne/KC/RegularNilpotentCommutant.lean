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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.RankThree.PartOne.KCRegular

open Matrix Module

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_cyclic_vector {N : Matrix ι ι K} {m : ℕ} (h : N ^ m ≠ 0) :
    ∃ v : ι → K, (N ^ m).mulVec v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  ext i j
  have := congrFun (hcon (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem linearIndependent_pow_mulVec {N : Matrix ι ι K} {n : ℕ} (hN0 : N ^ n = 0) {v : ι → K}
    (hv : (N ^ (n - 1)).mulVec v ≠ 0) :
    LinearIndependent K (fun j : Fin n => (N ^ (j : ℕ)).mulVec v) := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have h0 : N ^ (0 - 1) = 0 := by simpa using hN0
      rw [h0] at hv
      simp at hv
    · exact h
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hpow : ∀ a b : ℕ, (N ^ a).mulVec ((N ^ b).mulVec v) = (N ^ (a + b)).mulVec v := by
    intro a b
    rw [Matrix.mulVec_mulVec, ← pow_add]
  have hkill : ∀ c : ℕ, n ≤ c → (N ^ c).mulVec v = 0 := by
    intro c hc
    rw [← Nat.sub_add_cancel hc, pow_add, hN0, mul_zero, Matrix.zero_mulVec]
  have key : ∀ i : ℕ, ∀ hi : i < n, g ⟨i, hi⟩ = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have h1 := congrArg (fun w => (N ^ (n - 1 - i)).mulVec w) hg
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_zero] at h1
      rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin n)] at h1
      · rw [hpow] at h1
        have h2 : n - 1 - i + i = n - 1 := by omega
        rw [h2] at h1
        exact (smul_eq_zero.mp h1).resolve_right hv
      · intro j _ hj
        by_cases hji : (j : ℕ) < i
        · rw [ih j hji j.2, zero_smul]
        · have hji' : i < (j : ℕ) := by
            rcases Nat.lt_or_ge i j with h | h
            · exact h
            · exact absurd (Fin.ext (by simp only; omega)) hj
          rw [hpow, hkill _ (by omega), smul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
  intro j
  exact key j j.2

theorem exists_eq_sum_pow_of_commute [Nonempty ι] {N : Matrix ι ι K} (hN0 : N ^ Fintype.card ι = 0)
    (hN1 : N ^ (Fintype.card ι - 1) ≠ 0) {M : Matrix ι ι K} (hM : Commute M N) :
    ∃ c : Fin (Fintype.card ι) → K, M = ∑ j : Fin (Fintype.card ι), c j • N ^ (j : ℕ) := by
  classical
  set n := Fintype.card ι with hn
  obtain ⟨v, hv⟩ := exists_cyclic_vector hN1
  have hli := linearIndependent_pow_mulVec hN0 hv
  have hcard : Fintype.card (Fin n) = Module.finrank K (ι → K) := by
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card]
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hMv : M.mulVec v ∈ Submodule.span K (Set.range
      (fun j : Fin n => (N ^ (j : ℕ)).mulVec v)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hMv
  refine ⟨c, ?_⟩
  set P : Matrix ι ι K := ∑ j : Fin n, c j • N ^ (j : ℕ) with hP
  have hPv : P.mulVec v = M.mulVec v := by
    rw [← hc, hP]
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec]
  have hPN : Commute P N :=
    Commute.sum_left _ _ _ fun j _ => ((Commute.refl N).pow_left _).smul_left _
  have hagree : ∀ i : Fin n,
      M.mulVec ((N ^ (i : ℕ)).mulVec v) = P.mulVec ((N ^ (i : ℕ)).mulVec v) := by
    intro i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ((hM.symm.pow_left (i : ℕ)).symm).eq,
      ((hPN.symm.pow_left (i : ℕ)).symm).eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPv]
  have hb : M.mulVecLin = P.mulVecLin := by
    refine LinearMap.ext_on_range hspan fun i => ?_
    exact hagree i
  exact Matrix.toLin'.injective (by rw [Matrix.toLin'_apply', Matrix.toLin'_apply']; exact hb)

theorem commute_of_commute_regular [Nonempty ι] {N : Matrix ι ι K}
    (hN0 : N ^ Fintype.card ι = 0) (hN1 : N ^ (Fintype.card ι - 1) ≠ 0) {M₁ M₂ : Matrix ι ι K}
    (h1 : Commute M₁ N) (h2 : Commute M₂ N) : Commute M₁ M₂ := by
  obtain ⟨c, rfl⟩ := exists_eq_sum_pow_of_commute hN0 hN1 h1
  obtain ⟨d, rfl⟩ := exists_eq_sum_pow_of_commute hN0 hN1 h2
  refine Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
  exact (((Commute.refl N).pow_pow _ _).smul_left _).smul_right _

theorem exists_isNilpotent_sub_of_commute [Nonempty ι] {N : Matrix ι ι K}
    (hN0 : N ^ Fintype.card ι = 0) (hN1 : N ^ (Fintype.card ι - 1) ≠ 0) {M : Matrix ι ι K}
    (hM : Commute M N) : ∃ c₀ : K, IsNilpotent (M - c₀ • (1 : Matrix ι ι K)) := by
  classical
  obtain ⟨c, rfl⟩ := exists_eq_sum_pow_of_commute hN0 hN1 hM
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  refine ⟨c ⟨0, hn⟩, ?_⟩
  have h0 : ∑ j : Fin (Fintype.card ι), c j • N ^ (j : ℕ) - c ⟨0, hn⟩ • (1 : Matrix ι ι K) =
      ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (Fintype.card ι)), c j • N ^ (j : ℕ) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin (Fintype.card ι)))]
    simp
  rw [h0]
  refine Commute.isNilpotent_sum (fun j hj => ?_) (fun i j _ _ =>
    (((Commute.refl N).pow_pow _ _).smul_left _).smul_right _)
  have hj0 : (j : ℕ) ≠ 0 := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h)
  refine IsNilpotent.smul ?_ _
  exact ⟨Fintype.card ι, by rw [← pow_mul, mul_comm, pow_mul, hN0]; exact zero_pow hj0⟩

end CFSG.RankThree.PartOne.KCRegular
