module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientBM
import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientKernelElimination
import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingAlternatives
import CFSG.RankThree.PartOne.S10.NonquasisimpleMovingScalarKernelHyperplane

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem five_shape {G : Type} [Group G] [Finite G] {q : ℕ} {A₀ D R : Subgroup G}
    (hTwo : TwoActionInputs) (hset : MinTwoActionSetting 5 q A₀ D R)
    (hrank : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ centralizer ({r} : Set G)) ≤ 3) :
    (CFSG.IsElementaryAbelian 2 R ∧ Nat.card R = 16 ∧ CFSG.IsElementaryAbelian q D ∧
      Nat.card D = q ^ 5 ∧ ⁅D, R⁆ = D ∧ D ⊓ centralizer (R : Set G) = ⊥ ∧
      ∃ r ∈ R, orderOf r = 2 ∧ CFSG.pRank q ↥(D ⊓ centralizer ({r} : Set G)) = 3) ∨
    (∃ X : Subgroup G, X ≤ D ∧ R ≤ normalizer (X : Set G) ∧ ⁅X, R⁆ = X ∧
      A₀ ≤ normalizer (X : Set G) ∧
      (∃ a ∈ A₀, ∃ r ∈ R, a * r * a⁻¹ * r⁻¹ ∉ centralizer (X : Set G)) ∧
      ∃ ψ : ↥R →* QD32, Function.Surjective ψ ∧
        ψ.ker = (R ⊓ centralizer (X : Set G)).subgroupOf R) := by
  obtain ⟨X, hXD, hXR, hXirr, -, hKΦ, hAnt, hirrR, -, hshape, hB, -, -, -⟩ :=
    minimalTwoActionSmallFaithfulQuotient G 5 q A₀ D R hset hrank
  rcases hshape with ⟨hp7, -⟩ | ⟨-, hc, hs, hi⟩ | ⟨-, ψ, hψs, hψk⟩
  · omega
  · left
    obtain ⟨hRcase, hex, -, -, -⟩ := Lifting36.alternatives_elementary
      elementaryFaithfulQuotientKernelElimination hTwo.2.2 hset hrank (Or.inr ⟨rfl, rfl⟩) hXD hXirr
      hKΦ hirrR hc hs hi hB
    obtain ⟨hRe, hRcard⟩ : CFSG.IsElementaryAbelian 2 R ∧ Nat.card R = 16 := by
      rcases hRcase with ⟨-, hRe, hRcard⟩ | ⟨h7, -⟩
      · exact ⟨hRe, hRcard⟩
      · omega
    have hq := hset.prime_q
    have hA₀R : A₀ ≤ normalizer (R : Set G) := hset.R_inv
    have hA₀D : A₀ ≤ normalizer (D : Set G) := le_sup_right.trans hset.D_inv
    have hfrR : inSubgroup frattini R = ⊥ := by
      have : Fact (IsPGroup 2 ↥R) := ⟨hRe.isPGroup 2 ↥R⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [inSubgroup, frattini_eq_bot_of_isElementaryAbelian (p := 2), Subgroup.map_bot]
    have hodd : ¬ 2 ∣ Nat.card A₀ := by
      rw [hset.A_card]
      decide
    have hmin₀ : ∀ U : Subgroup G, U < R → A₀ ≤ normalizer (U : Set G) → ⁅U, A₀⁆ = U →
        ⁅U, D⁆ = ⊥ := fun U hU hA₀U hUA₀ =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hset.R_min U hU hA₀U hUA₀)
    have hirr : ∀ Y : Subgroup G, Y ≤ R → A₀ ≤ normalizer (Y : Set G) → Y = ⊥ ∨ Y = R := by
      intro Y hYR hA₀Y
      by_cases hYe : Y = R
      · exact Or.inr hYe
      refine Or.inl ?_
      have h' := le_inSubgroup_frattini_of_proper_invariant hset.R_two hset.R_ne hodd hA₀R hA₀D
        hset.R_comm hset.R_act hmin₀ Y (lt_of_le_of_ne hYR hYe) hA₀Y
      rw [hfrR] at h'
      exact le_bot_iff.mp h'
    obtain ⟨hRD, hDe, hDcard, hDR, hDC, -⟩ := hTwo.2.2 G 5 q 4 A₀ D R (by norm_num) hq
      hset.q_ne_two hset.p_ne_q.symm (Or.inr ⟨rfl, rfl⟩) hset.A_elem hset.A_card hA₀R hRe
      (by rw [hRcard]; norm_num) hB hirr hset.D_inv hset.D_pgroup hset.D_exp hset.D_class
      hset.R_act hrank
    refine ⟨hRe, hRcard, hDe, hDcard, hDR, hDC, ?_⟩
    obtain ⟨r, hrR, hr1, hr3⟩ := hex
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact ⟨r, hrR, orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) r hrR) hr1,
      hr3⟩
  · refine Or.inr ⟨X, hXD, le_sup_left.trans hXirr.1, hXR, le_sup_right.trans hXirr.1, ?_, ψ, hψs,
      hψk⟩
    obtain ⟨a, haA, r, hrR, hnot⟩ := hAnt
    refine ⟨a, haA, r, hrR, fun hc => hnot ?_⟩
    have hmem : a * r * a⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hset.R_inv haA) r).mp hrR
    have hcomm : ⁅a, r⁆ = a * r * a⁻¹ * r⁻¹ := commutatorElement_def a r
    rw [hcomm]
    exact hKΦ ⟨R.mul_mem hmem (R.inv_mem hrR), hc⟩

end CFSG.RankThree.PartOne.F106
