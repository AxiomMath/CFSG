module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG.RankThree.PartOne.KCUnitaryRegular

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

theorem pow_eq_zero_of_le {N : Matrix (Fin n) (Fin n) K} (hNn : N ^ n = 0) {m : ℕ} (hm : n ≤ m) :
    N ^ m = 0 := by
  rw [← Nat.add_sub_cancel' hm, pow_add, hNn, zero_mul]

theorem eq_zero_of_forall_mulVec_eq_zero {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ v, M *ᵥ v = 0) : M = 0 := by
  ext i j
  have h1 := congrFun (hM (Pi.single j 1)) i
  rwa [mulVec_single_one, col_apply] at h1

theorem linearIndependent_pow_mulVec {N : Matrix (Fin n) (Fin n) K} (hNn : N ^ n = 0)
    {v : Fin n → K} (hv : (N ^ (n - 1)) *ᵥ v ≠ 0) :
    LinearIndependent K (fun k : Fin n => (N ^ (k : ℕ)) *ᵥ v) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ m : ℕ, ∀ hm : m < n, g ⟨m, hm⟩ = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have h1 : (N ^ (n - 1 - m)) *ᵥ (∑ j, g j • (N ^ (j : ℕ)) *ᵥ v) = 0 := by
        rw [hg, mulVec_zero]
      rw [mulVec_sum] at h1
      simp only [mulVec_smul, mulVec_mulVec, ← pow_add] at h1
      rw [Finset.sum_eq_single ⟨m, hm⟩] at h1
      · have h2 : n - 1 - m + m = n - 1 := by omega
        simp only [h2] at h1
        exact (smul_eq_zero.mp h1).resolve_right hv
      · intro j _ hj
        rcases lt_or_gt_of_ne (fun e => hj (Fin.ext e) : (j : ℕ) ≠ m) with hjm | hjm
        · have hgj : g j = 0 := ih j hjm j.isLt
          rw [hgj, zero_smul]
        · rw [pow_eq_zero_of_le hNn (by omega), zero_mulVec, smul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
  intro j
  exact key j j.isLt

theorem exists_eq_sum_pow_of_commute {N A : Matrix (Fin n) (Fin n) K} (hn : 1 ≤ n)
    (hNn : N ^ n = 0) (hNreg : N ^ (n - 1) ≠ 0) (hA : A * N = N * A) :
    ∃ c : Fin n → K, A = ∑ k : Fin n, c k • N ^ (k : ℕ) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨v, hv⟩ : ∃ v, (N ^ (n - 1)) *ᵥ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hNreg (eq_zero_of_forall_mulVec_eq_zero hcon)
  have hli := linearIndependent_pow_mulVec hNn hv
  have hspan : Submodule.span K (Set.range fun k : Fin n => (N ^ (k : ℕ)) *ᵥ v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by rw [Module.finrank_fin_fun, Fintype.card_fin])
  have hmem : A *ᵥ v ∈ Submodule.span K (Set.range fun k : Fin n => (N ^ (k : ℕ)) *ᵥ v) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
  refine ⟨c, ?_⟩
  have hAN : Commute A N := hA
  have hcomm : ∀ j : ℕ, A * N ^ j = N ^ j * A := fun j => (hAN.pow_right j).eq
  have hAP : ∀ j : Fin n, A *ᵥ ((N ^ (j : ℕ)) *ᵥ v) =
      (∑ k : Fin n, c k • N ^ (k : ℕ)) *ᵥ ((N ^ (j : ℕ)) *ᵥ v) := by
    intro j
    rw [mulVec_mulVec, hcomm, ← mulVec_mulVec, ← hc, mulVec_sum, sum_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulVec_smul, smul_mulVec, mulVec_mulVec, mulVec_mulVec, ← pow_add, ← pow_add, add_comm]
  have hlin : A.mulVecLin = (∑ k : Fin n, c k • N ^ (k : ℕ)).mulVecLin :=
    LinearMap.ext_on hspan (by
      rintro _ ⟨j, rfl⟩
      exact hAP j)
  exact Matrix.toLin'.injective hlin

theorem exists_isNilpotent_sub_smul_one_of_commute {N A : Matrix (Fin n) (Fin n) K}
    (hn : 1 ≤ n) (hNn : N ^ n = 0) (hNreg : N ^ (n - 1) ≠ 0) (hA : A * N = N * A) :
    ∃ l : K, IsNilpotent (A - l • (1 : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨c, hc⟩ := exists_eq_sum_pow_of_commute hn hNn hNreg hA
  refine ⟨c ⟨0, hn⟩, ?_⟩
  have h0 : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hsplit : A - c ⟨0, hn⟩ • (1 : Matrix (Fin n) (Fin n) K) =
      ∑ k ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), c k • N ^ (k : ℕ) := by
    rw [hc, ← Finset.add_sum_erase _ _ h0]
    simp
  rw [hsplit]
  refine Commute.isNilpotent_sum (fun k hk => ?_) (fun i j _ _ => ?_)
  · have hk0 : 1 ≤ (k : ℕ) := by
      have := Finset.ne_of_mem_erase hk
      have : (k : ℕ) ≠ 0 := fun e => this (Fin.ext e)
      omega
    refine ⟨n, ?_⟩
    rw [smul_pow, ← pow_mul, pow_eq_zero_of_le hNn (by nlinarith), smul_zero]
  · exact ((Commute.refl N).pow_pow (i : ℕ) (j : ℕ)).smul_left (c i) |>.smul_right (c j)

end CFSG.RankThree.PartOne.KCUnitaryRegular
