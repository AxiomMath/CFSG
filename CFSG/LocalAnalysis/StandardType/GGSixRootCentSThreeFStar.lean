module

public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.StandardType

variable {Y : Type*} [Group Y] [Finite Y]

private theorem solvable_of_mulEquiv {X Z : Type*} [Group X] [Group Z] (e : X ≃* Z)
    [Group.IsSolvable Z] : Group.IsSolvable X :=
  Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem ggSThree_layer_le_centralizer {H A : Subgroup Y}
    (hcomp : ∀ K : Subgroup Y, CFSG.IsComponent K → K ≤ H) (hAH : A ≤ H)
    (hAn : ∀ h ∈ H, ∀ a ∈ A, h * a * h⁻¹ ∈ A) (hAs : Group.IsSolvable A) :
    CFSG.layer Y ≤ Subgroup.centralizer (A : Set Y) := by
  rw [CFSG.layer.eq_sSup Y]
  refine sSup_le fun K hK => (Subgroup.commutator_eq_bot_iff_le_centralizer.mp ?_)
  have hKH : K ≤ H := hcomp K hK
  haveI : Group.IsSolvable A := hAs
  have hsol : Group.IsSolvable (A.subgroupOf H) :=
    solvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAH)
  have hnorm : (A.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff hAH).mpr fun a h ha hh => hAn h hh a ha
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer (G := ↥H) hsol
    hnorm.isSubnormal).1 (K.subgroupOf H) (CFSG.LocalCores.component_overgroup hK hKH)
  have h2 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf (K := K) (H := A)
    (L := H) hKH hcomm
  rwa [inf_eq_left.mpr hAH] at h2

theorem ggSThree_le_fitting_of_centralizes {A : Subgroup Y}
    (hL : CFSG.layer Y ≤ Subgroup.centralizer (A : Set Y))
    (hF : CFSG.fittingSubgroup Y ≤ Subgroup.centralizer (A : Set Y)) :
    A ≤ CFSG.fittingSubgroup Y := by
  intro a ha
  have haF : a ∈ Subgroup.centralizer (CFSG.fittingSubgroup Y : Set Y) :=
    (Subgroup.le_centralizer_iff.mp hF) ha
  have haE : a ∈ Subgroup.centralizer (CFSG.layer Y : Set Y) :=
    (Subgroup.le_centralizer_iff.mp hL) ha
  have haGen : a ∈ Subgroup.centralizer
      ((CFSG.fittingSubgroup Y ⊔ CFSG.layer Y : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨f, hf, l, hl, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    have hf' : f * a = a * f := (Subgroup.mem_centralizer_iff.mp haF) f hf
    have hl' : l * a = a * l := (Subgroup.mem_centralizer_iff.mp haE) l hl
    calc f * l * a = f * (l * a) := by rw [mul_assoc]
      _ = f * (a * l) := by rw [hl']
      _ = f * a * l := by rw [mul_assoc]
      _ = a * f * l := by rw [hf']
      _ = a * (f * l) := by rw [mul_assoc]
  have haGen' : a ∈ Subgroup.centralizer (CFSG.generalizedFitting Y : Set Y) := by
    rwa [CFSG.generalizedFitting.eq_sup Y]
  have haG : a ∈ CFSG.generalizedFitting Y :=
    CFSG.centralizer_generalizedFitting_le Y haGen'
  rw [CFSG.generalizedFitting.eq_sup Y] at haG
  obtain ⟨f, hf, l, hl, hfl⟩ := Subgroup.mem_sup_of_normal_left.mp haG
  have hfE : f ∈ Subgroup.centralizer (CFSG.layer Y : Set Y) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.LocalCores.fitting_layer_commute (G := Y))) hf
  have hlC : l ∈ Subgroup.centralizer (CFSG.layer Y : Set Y) := by
    have hmem : f⁻¹ * a ∈ Subgroup.centralizer (CFSG.layer Y : Set Y) :=
      mul_mem (inv_mem hfE) haE
    have h : f⁻¹ * (f * l) ∈ Subgroup.centralizer (CFSG.layer Y : Set Y) := by
      rwa [← hfl] at hmem
    simpa only [inv_mul_cancel_left] using h
  have hlZ : l ∈ (Subgroup.center (CFSG.layer Y)).map (CFSG.layer Y).subtype :=
    (CFSG.LocalCores.mem_map_center_iff (CFSG.layer Y)).mpr ⟨hl, hlC⟩
  have hlF : l ∈ CFSG.fittingSubgroup Y :=
    CFSG.WholeGroup.center_layer_le_fittingSubgroup hlZ
  have hflF : f * l ∈ CFSG.fittingSubgroup Y := mul_mem hf hlF
  rwa [hfl] at hflF

theorem ggSThree_eq_bot_of_inf_fitting_eq_bot {H A : Subgroup Y}
    (hFH : CFSG.fittingSubgroup Y ≤ H)
    (hcomp : ∀ K : Subgroup Y, CFSG.IsComponent K → K ≤ H) (hAH : A ≤ H)
    (hAn : ∀ h ∈ H, ∀ a ∈ A, h * a * h⁻¹ ∈ A) (hAs : Group.IsSolvable A)
    (hAF : A ⊓ CFSG.fittingSubgroup Y = ⊥) : A = ⊥ := by
  have hF : CFSG.fittingSubgroup Y ≤ Subgroup.centralizer (A : Set Y) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hcA : f * a * f⁻¹ * a⁻¹ ∈ A :=
      mul_mem (hAn f (hFH hf) a ha) (inv_mem ha)
    have hcF : f * a * f⁻¹ * a⁻¹ ∈ CFSG.fittingSubgroup Y := by
      have hd : a * f⁻¹ * a⁻¹ ∈ CFSG.fittingSubgroup Y :=
        (inferInstance : (CFSG.fittingSubgroup Y).Normal).conj_mem f⁻¹ (inv_mem hf) a
      simpa only [mul_assoc] using mul_mem hf hd
    have hc : f * a * f⁻¹ * a⁻¹ ∈ A ⊓ CFSG.fittingSubgroup Y := ⟨hcA, hcF⟩
    have hc1 : f * a * f⁻¹ * a⁻¹ = 1 := by
      rw [hAF] at hc
      exact Subgroup.mem_bot.mp hc
    have hfa : f * a = a * f := by
      have h1 : f * a * (a * f)⁻¹ = 1 := by
        rw [mul_inv_rev]
        simpa only [mul_assoc] using hc1
      exact mul_inv_eq_one.mp h1
    exact hfa.symm
  have hL : CFSG.layer Y ≤ Subgroup.centralizer (A : Set Y) :=
    ggSThree_layer_le_centralizer hcomp hAH hAn hAs
  exact (inf_eq_left.mpr (ggSThree_le_fitting_of_centralizes hL hF)).symm.trans hAF

theorem ggSThree_eq_bot_of_two_group {H A : Subgroup Y} (hO : CFSG.pPrimeCore 3 Y = ⊥)
    (hFH : CFSG.fittingSubgroup Y ≤ H)
    (hcomp : ∀ K : Subgroup Y, CFSG.IsComponent K → K ≤ H) (hAH : A ≤ H)
    (hAn : ∀ h ∈ H, ∀ a ∈ A, h * a * h⁻¹ ∈ A) (hA2 : IsPGroup 2 A) : A = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : IsPGroup 3 (CFSG.fittingSubgroup Y) := by
    rw [CFSG.Fitting_eq_pcore Y 3 hO]
    exact CFSG.pCore_isPGroup (p := 3) (G := Y)
  have hdisj : Disjoint A (CFSG.fittingSubgroup Y) :=
    IsPGroup.disjoint_of_ne 2 3 (by norm_num) A (CFSG.fittingSubgroup Y) hA2 hF3
  have hAs : Group.IsSolvable A := by
    have : Group.IsNilpotent A := hA2.isNilpotent
    infer_instance
  exact ggSThree_eq_bot_of_inf_fitting_eq_bot hFH hcomp hAH hAn hAs hdisj.eq_bot

theorem ggSThree_le_fitting_of_card_dvd_three {H A : Subgroup Y}
    (hFH : CFSG.fittingSubgroup Y ≤ H)
    (hcomp : ∀ K : Subgroup Y, CFSG.IsComponent K → K ≤ H) (hAH : A ≤ H)
    (hAn : ∀ h ∈ H, ∀ a ∈ A, h * a * h⁻¹ ∈ A) (hAs : Group.IsSolvable A)
    (hA3 : Nat.card A ∣ 3) : A ≤ CFSG.fittingSubgroup Y := by
  by_cases hAF : A ⊓ CFSG.fittingSubgroup Y = ⊥
  · rw [ggSThree_eq_bot_of_inf_fitting_eq_bot hFH hcomp hAH hAn hAs hAF]
    exact bot_le
  · have h1 : 1 < Nat.card ↥(A ⊓ CFSG.fittingSubgroup Y) :=
      (Subgroup.one_lt_card_iff_ne_bot (A ⊓ CFSG.fittingSubgroup Y)).mpr hAF
    have hdvd : Nat.card ↥(A ⊓ CFSG.fittingSubgroup Y) ∣ 3 :=
      (Subgroup.card_dvd_of_le (inf_le_left : A ⊓ CFSG.fittingSubgroup Y ≤ A)).trans hA3
    have hcard3 : Nat.card ↥(A ⊓ CFSG.fittingSubgroup Y) = 3 := by
      rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h | h
      · omega
      · exact h
    have hcardA : Nat.card A = 3 :=
      (Nat.dvd_antisymm (hcard3 ▸ Subgroup.card_dvd_of_le
        (inf_le_left : A ⊓ CFSG.fittingSubgroup Y ≤ A)) hA3).symm
    have hEq : A ⊓ CFSG.fittingSubgroup Y = A :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : A ⊓ CFSG.fittingSubgroup Y ≤ A) (by omega)
    exact hEq ▸ inf_le_right

end CFSG.StandardType
