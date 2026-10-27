module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import CFSG.GroupTheory.CoprimeCosetFixed
import CFSG.LieType.BorelTits.Basic
import CFSG.LocalAnalysis.StandardType.FS81.L3TwoFixedPointFree
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.QuasithinUnique

theorem fixedPointFree_quotient_of_inf_centralizer_le {X : Type} [Group X] [Finite X]
    {S T T₀ T₁ : Subgroup X} {b : X}
    (hTS : T ⊓ Subgroup.centralizer ({b} : Set X) ≤ S)
    (hbN : b ∈ Subgroup.normalizer (T₀ : Set X)) (hb3 : orderOf b = 3)
    (hT2 : IsPGroup 2 T) (hT₀ : T₀ = T ⊓ S)
    (hT₁ : T₁ = T ⊓ Subgroup.normalizer (T₀ : Set X)) :
    ∀ t' ∈ T₁, b * t' * b⁻¹ * t'⁻¹ ∈ T₀ → t' ∈ T₀ := by
  intro t' ht' hmem
  have ht'T : t' ∈ T := by rw [hT₁] at ht'; exact ht'.1
  have ht'N : t' ∈ Subgroup.normalizer (T₀ : Set X) := by rw [hT₁] at ht'; exact ht'.2
  have hT₀2 : IsPGroup 2 T₀ := by rw [hT₀]; exact hT2.to_le inf_le_left
  have hN : ∀ n ∈ T₀, b * n * b⁻¹ ∈ T₀ := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp hbN n).mp hn
  have hg : t'⁻¹ * (b * t' * b⁻¹) ∈ T₀ := by
    have h1 : t'⁻¹ * (b * t' * b⁻¹) = t'⁻¹ * (b * t' * b⁻¹ * t'⁻¹) * t' := by
      group
    rw [h1]
    have h2 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (T₀ : Set X)).inv_mem ht'N)
      (b * t' * b⁻¹ * t'⁻¹)).mp hmem
    simpa using h2
  have h3 : ¬ 3 ∣ Nat.card T₀ := by
    intro h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT₀2
    rw [hk] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hcop : Nat.Coprime (orderOf b) (Nat.card T₀) := by
    rw [hb3]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  obtain ⟨n, hnT₀, hfixn⟩ :=
    CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime (N := T₀) hN hg hcop
  have hnT : n ∈ T := by rw [hT₀] at hnT₀; exact hnT₀.1
  have hnS : n ∈ S := by rw [hT₀] at hnT₀; exact hnT₀.2
  have hzT : t' * n ∈ T := T.mul_mem ht'T hnT
  have hzC : t' * n ∈ Subgroup.centralizer ({b} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : b * (t' * n) = (t' * n) * b := by
      calc b * (t' * n) = b * (t' * n) * b⁻¹ * b := by group
        _ = (t' * n) * b := by rw [hfixn]
    exact hcomm.symm
  have hzS : t' * n ∈ S := hTS ⟨hzT, hzC⟩
  have ht'S : t' ∈ S := by
    have h : t' = (t' * n) * n⁻¹ := by group
    rw [h]
    exact S.mul_mem hzS (S.inv_mem hnS)
  rw [hT₀]
  exact ⟨ht'T, ht'S⟩

theorem zpowers_le_pCoreOf_centralizer {X : Type} [Group X] [Finite X]
    {t₀ : X} (ht₀ : orderOf t₀ = 2) :
    Subgroup.zpowers t₀ ≤ pCoreOf 2 (Subgroup.centralizer ({t₀} : Set X)) := by
  have hct : ∀ c ∈ Subgroup.centralizer ({t₀} : Set X), Commute c t₀ := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc
    exact (hc t₀ (by simp)).symm
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
    (N := Subgroup.zpowers t₀) (H := Subgroup.centralizer ({t₀} : Set X)) ?_ ?_ ?_
  · refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    rfl
  · intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [Subgroup.mem_zpowers_iff] at hz ⊢
      obtain ⟨k, rfl⟩ := hz
      exact ⟨k, ((hct c hc).zpow_right k).mul_inv_cancel.symm⟩
    · intro hz
      rw [Subgroup.mem_zpowers_iff] at hz ⊢
      obtain ⟨k, hk⟩ := hz
      refine ⟨k, ?_⟩
      rw [show z = c⁻¹ * (c * z * c⁻¹) * c from by group, ← hk]
      simpa using ((hct c hc).inv_left.zpow_right k).mul_inv_cancel.symm
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht₀]
    norm_num

private theorem rootO2_pCore_eq {X : Type} [Group X] [Finite X]
    {U T L : Subgroup X} {t₀ b : X}
    (hirr : ∀ V : Subgroup X, Subgroup.zpowers t₀ ≤ V → V ≤ U →
      L ≤ Subgroup.normalizer (V : Set X) → V = Subgroup.zpowers t₀ ∨ V = U)
    (hcharT : Subgroup.centralizer ({t₀} : Set X) ⊓
      Subgroup.centralizer (T : Set X) ≤ T)
    (ht₀ : orderOf t₀ = 2) (hTU : T ≤ U) (hLT : L ≤ Subgroup.normalizer (T : Set X))
    (hzT : Subgroup.zpowers t₀ ≤ T) (hbH : b ∈ Subgroup.centralizer ({t₀} : Set X))
    (hb3 : orderOf b = 3) : T = U := by
  rcases hirr T hzT hTU hLT with h | h
  · exfalso
    have hbCT : b ∈ Subgroup.centralizer (T : Set X) := by
      rw [h, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hbH
    have hbT : b ∈ T := hcharT ⟨hbH, hbCT⟩
    have h3dvd : 3 ∣ Nat.card (Subgroup.zpowers t₀) := by
      rw [← hb3]
      exact Subgroup.orderOf_dvd_natCard _ (by rw [← h]; exact hbT)
    rw [Nat.card_zpowers, ht₀] at h3dvd
    norm_num at h3dvd
  · exact h

theorem pCoreOf_centralizer_eq_of_inf_centralizer_le {X : Type} [Group X] [Finite X]
    {U L P : Subgroup X} {b t₀ : X} (ht₀ : orderOf t₀ = 2)
    (hLt₀ : L ≤ Subgroup.centralizer ({t₀} : Set X)) (hLU : L ≤ Subgroup.normalizer (U : Set X))
    (hirr : ∀ V : Subgroup X, Subgroup.zpowers t₀ ≤ V → V ≤ U →
      L ≤ Subgroup.normalizer (V : Set X) → V = Subgroup.zpowers t₀ ∨ V = U)
    (hb : orderOf b = 3) (hbP : b ∈ P) (hPL : P ≤ L)
    (hP : Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hTU : pCoreOf 2 (Subgroup.centralizer ({t₀} : Set X)) ⊓
      Subgroup.centralizer ({b} : Set X) ≤ U)
    (hChar : CharTwo (Subgroup.centralizer ({t₀} : Set X))) :
    pCoreOf 2 (Subgroup.centralizer ({t₀} : Set X)) = U := by
  classical
  let H : Subgroup X := Subgroup.centralizer ({t₀} : Set X)
  let T : Subgroup X := pCoreOf 2 H
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H
  have hTN : H ≤ Subgroup.normalizer (T : Set X) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H
  have hLN : L ≤ Subgroup.normalizer (T : Set X) := hLt₀.trans hTN
  let T₀ : Subgroup X := T ⊓ U
  let T₁ : Subgroup X := T ⊓ Subgroup.normalizer (T₀ : Set X)
  have hLNT₀ : L ≤ Subgroup.normalizer (T₀ : Set X) :=
    (le_inf hLN hLU).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := T) (K := U))
  have hLNT₁ : L ≤ Subgroup.normalizer (T₁ : Set X) :=
    (le_inf hLN (hLNT₀.trans Subgroup.le_normalizer)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := T)
        (K := Subgroup.normalizer (T₀ : Set X)))
  have hfpf : ∀ t' ∈ T₁, b * t' * b⁻¹ * t'⁻¹ ∈ T₀ → t' ∈ T₀ :=
    fixedPointFree_quotient_of_inf_centralizer_le (S := U) hTU
      (hLNT₀ (hPL hbP)) hb hT2 rfl rfl
  haveI : Group.IsNilpotent ↥T₁ := IsPGroup.isNilpotent (hT2.to_le inf_le_left)
  have hsol : IsSolvable ↥T₁ := IsNilpotent.to_isSolvable
  have hT₁le : T₁ ≤ T₀ :=
    le_of_l3TwoFixedPointFree (le_inf inf_le_left Subgroup.le_normalizer) inf_le_right
      (hPL.trans hLNT₁) (hPL.trans hLNT₀) hP hbP hb hsol hfpf
  have hT₀eqT : T₀ = T := by
    by_contra hne
    have hlt : T₀ < T := lt_of_le_of_ne inf_le_left hne
    have hgrowth : T₀ < T ⊓ Subgroup.normalizer (T₀ : Set X) :=
      CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime.pSubgroup_lt_normalizer_intersection
        2 Nat.prime_two T₀ T hT2 hlt
    have hle : T ⊓ Subgroup.normalizer (T₀ : Set X) ≤ T₀ := hT₁le
    exact not_le_of_gt hgrowth hle
  have hTU' : T ≤ U := by rw [← hT₀eqT]; exact inf_le_right
  have hzT : Subgroup.zpowers t₀ ≤ T := zpowers_le_pCoreOf_centralizer ht₀
  have hcharT : H ⊓ Subgroup.centralizer (T : Set X) ≤ T := hChar
  exact rootO2_pCore_eq hirr hcharT ht₀ hTU' hLN hzT (hLt₀ (hPL hbP)) hb

end CFSG.StandardType.FrameRoute.FS81
