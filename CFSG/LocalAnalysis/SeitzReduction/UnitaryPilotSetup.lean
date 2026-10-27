module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotKernel
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamilies
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalUnitary
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherClassicalSchreier

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.EvenSmallLie
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitaryPSUEquiv)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)

section Model

theorem exists_mulEquiv_unitaryPSU_of_lieModel {X : Type} [Group X] {n f : ℕ}
    (hX : CFSG.Blueprint.LieModel X .PSU n 2 f) :
    3 ≤ n ∧ (n, 2 ^ f) ≠ (3, 2) ∧
      ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K), Nonempty (X ≃* unitaryPSU h n) := by
  rcases hX with ⟨-, ⟨-, hf, hn, hnq⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    exact ⟨hn, hnq, K, inferInstance, h, ⟨e.trans (unitaryPSUEquiv h (by omega)).symm⟩⟩
  · simp [CFSG.Blueprint.chevalleyExceptionalTags] at ht
  · simp [CFSG.Blueprint.reeTitsTags] at ht
  · cases ht

end Model

section Outer

theorem isSolvable_outer_of_lieModel {X : Type} [Group X] {n f : ℕ}
    (hX : CFSG.Blueprint.LieModel X .PSU n 2 f) : Group.IsSolvable (Outer X) := by
  rcases hX with ⟨-, hX⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_classical_model_schreier
      hX).2
  · simp [CFSG.Blueprint.chevalleyExceptionalTags] at ht
  · simp [CFSG.Blueprint.reeTitsTags] at ht
  · cases ht

theorem isSolvable_outer_of_mulEquiv {X : Type} [Group X] {p f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hn : 3 ≤ n) (hnq : (n, p ^ f) ≠ (3, 2))
    (e : X ≃* unitaryPSU h n) : Group.IsSolvable (Outer X) :=
  (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_classical_model_schreier
    (H := X) (n := n) (p := p) (f := f)
    ⟨⟨h.prime, h.one_le, hn, hnq⟩, K, inferInstance, h.finite, h.card_eq_sq,
      ⟨e.trans (unitaryPSUEquiv h (by omega))⟩⟩).2

end Outer

section Kernel

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem hypothesisOne_quotient_center (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (e : L ≃* unitaryPSU h n) (hn : 5 ≤ n) :
    HypothesisOne (L ⧸ center L) :=
  hypothesisOne_of_mulEquiv (e.symm.trans (quotientCenterMulEquiv hset.center_eq_bot).symm)
    (hypothesisOne_unitaryPSU h hn)

theorem inf_centralizer_eq_zpowers (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (e : L ≃* unitaryPSU h n) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
  inf_centralizer_eq_zpowers_of_standard_of_center_eq_bot hset.standardSetting
    hset.center_eq_bot (hypothesisOne_quotient_center hset e hn) htC ht

theorem kernel (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (e : L ≃* unitaryPSU h n) (hn : 5 ≤ n) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (L : Set G) ∧
      (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) ∧
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
      centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      (∀ u ∈ centralizer (L : Set G), orderOf u = 2 →
        ∃ c ∈ centralizer (L : Set G), Odd (orderOf c) ∧ c * t * c⁻¹ = u) ∧
      ∀ x ∈ centralizer (L : Set G), Odd (orderOf x) → t * x * t⁻¹ = x⁻¹ :=
  F4Pilot.kernel hset.standardSetting hset.center_eq_bot (hypothesisOne_quotient_center hset e hn)

omit [Finite G] in
theorem not_mem_of_mem_centralizer_of_orderOf_eq_two (hZ : center L = ⊥) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) : t ∉ L := by
  intro htL
  have hz : (⟨t, htL⟩ : L) ∈ center L :=
    mem_center_iff.2 fun l => Subtype.ext (mem_centralizer_iff.1 htC l l.2)
  rw [hZ, mem_bot] at hz
  have h1 : t = 1 := congrArg Subtype.val hz
  rw [h1, orderOf_one] at ht
  exact absurd ht (by decide)

end Kernel

section Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_setup_of_five_le (hset : SeitzSetting G L) {n f : ℕ} (hn : 5 ≤ n)
    (hL : CFSG.Blueprint.LieModel L .PSU n 2 f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K),
      Nonempty (L ≃* unitaryPSU h n) ∧ Group.IsSolvable (Outer L) ∧
        ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (L : Set G) ∧ t ∉ L ∧
          (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) ∧
          centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
          centralizer ({t} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨-, -, K, _, h, ⟨e⟩⟩ := exists_mulEquiv_unitaryPSU_of_lieModel hL
  obtain ⟨t, ht, htC, hsyl, hKt, hCtN, -⟩ := kernel hset e hn
  exact ⟨K, inferInstance, h, ⟨e⟩, isSolvable_outer_of_lieModel hL, t, ht, htC,
    not_mem_of_mem_centralizer_of_orderOf_eq_two hset.center_eq_bot htC ht, hsyl, hKt, hCtN⟩

theorem exists_setup (hset : SeitzSetting G L) {n f : ℕ} (hn : 6 ≤ n)
    (hL : CFSG.Blueprint.LieModel L .PSU n 2 f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K), Nonempty (L ≃* unitaryPSU h n) ∧
      Group.IsSolvable (Outer L) ∧
      ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (L : Set G) ∧
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
        centralizer ({t} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨K, _, h, he, hout, t, ht, htC, -, -, hKt, hCtN⟩ :=
    exists_setup_of_five_le hset (by omega) hL
  exact ⟨K, inferInstance, h, he, hout, t, ht, htC, hKt, hCtN⟩

end Setup

theorem seitzExclusion_highPSU_of_forall
    (H : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K), 6 ≤ n → (n, f) ≠ (6, 1) →
        (L ≃* unitaryPSU h n) → ∀ t : G, orderOf t = 2 → t ∈ centralizer (L : Set G) →
          centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False) :
    SeitzExclusion HighPSU := by
  rintro G _ _ L hset ⟨n, f, hn, hnf, hL⟩
  obtain ⟨K, _, h, ⟨e⟩, -, t, ht, htC, hKt, -⟩ := exists_setup hset hn hL
  exact H G L hset n f K h hn hnf e t ht htC hKt

end CFSG.SeitzReduction.UnitaryPilot
