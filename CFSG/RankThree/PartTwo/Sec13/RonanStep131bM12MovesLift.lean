module

import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesElem
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open scoped Pointwise

theorem eq_one_of_mem_of_pow_three_pow {G : Type} [Group G] {N : Subgroup G}
    (hN : ¬ 3 ∣ Nat.card N) {g : G} (hg : g ∈ N) {k : ℕ} (hk : g ^ 3 ^ k = 1) : g = 1 := by
  have h1 : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf g ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hg
  have hcop : Nat.Coprime (3 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem s2lift_holds :
    ∀ (G : Type) [Group G] [Finite G] (Θ E : Subgroup G) (ρ' : G),
      ¬ 3 ∣ Nat.card Θ → IsPGroup 3 E → E ≤ Subgroup.normalizer (Θ : Set G) →
      ρ' ∈ Subgroup.normalizer (Θ : Set G) →
      ρ' ∈ Subgroup.normalizer ((E ⊔ Θ : Subgroup G) : Set G) → ρ' ^ 3 ∈ Θ →
      ∃ ρ : G, ρ'⁻¹ * ρ ∈ Θ ∧ ρ ^ 3 = 1 ∧ ρ ∈ Subgroup.normalizer (E : Set G) := by
  intro G _ _ Θ E ρ' hΘ3 hE3 hEΘ hρΘ hρM hρ3
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M : Subgroup G := E ⊔ Θ with hM
  have hEM : E ≤ M := le_sup_left
  have hΘM : Θ ≤ M := le_sup_right
  set E' : Subgroup G := E.map (MulAut.conj ρ').toMonoidHom with hE'
  have hE'M : E' ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hρM x).mp (hEM hx)
  have hEΘbot : E ⊓ Θ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := hE3 ⟨x, hx.1⟩
    exact (Subgroup.mem_bot.mpr (eq_one_of_mem_of_pow_three_pow hΘ3 hx.2
      (by simpa using congrArg Subtype.val hk)))
  have hMcard : Nat.card M = Nat.card E * Nat.card Θ := by
    have h := Sec6.card_sup_mul_card_inf hEΘ
    rw [hEΘbot, Subgroup.card_bot, mul_one] at h
    exact h
  have hEpos : 0 < Nat.card E := Nat.card_pos
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj ρ').injective
  have hEcardM : Nat.card (E.subgroupOf M) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv
  have hE'cardM : Nat.card (E'.subgroupOf M) = Nat.card E := by
    rw [← hE'card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'M).toEquiv
  have hidx : ∀ S : Subgroup M, Nat.card S = Nat.card E → ¬ 3 ∣ S.index := by
    intro S hS
    have h := Subgroup.index_mul_card S
    rw [hS, hMcard, mul_comm] at h
    have h2 : S.index = Nat.card Θ := Nat.eq_of_mul_eq_mul_left hEpos h
    rw [h2]
    exact hΘ3
  have hp₁ : IsPGroup 3 (E.subgroupOf M) := hE3.of_equiv (Subgroup.subgroupOfEquivOfLe hEM).symm
  have hp₂ : IsPGroup 3 (E'.subgroupOf M) :=
    (hE3.map (MulAut.conj ρ').toMonoidHom).of_equiv (Subgroup.subgroupOfEquivOfLe hE'M).symm
  let P₁ : Sylow 3 M := IsPGroup.toSylow hp₁ (hidx _ hEcardM)
  let P₂ : Sylow 3 M := IsPGroup.toSylow hp₂ (hidx _ hE'cardM)
  have hP₁ : (P₁ : Subgroup M) = E.subgroupOf M := IsPGroup.toSylow_coe _ _
  have hP₂ : (P₂ : Subgroup M) = E'.subgroupOf M := IsPGroup.toSylow_coe _ _
  haveI : Finite (Sylow 3 M) := Sylow.finite_of_finiteIndex P₁
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M P₁ P₂
  have hmS : MulAut.conj m • (P₁ : Subgroup M) = (P₂ : Subgroup M) := by
    rw [← Sylow.coe_subgroup_smul, hm]
  have hmE : ∀ e ∈ E, ∃ x ∈ E, ρ' * x * ρ'⁻¹ = (m : G) * e * (m : G)⁻¹ := by
    intro e he
    have hx : (⟨e, hEM he⟩ : M) ∈ (P₁ : Subgroup M) := by
      rw [hP₁]
      exact Subgroup.mem_subgroupOf.mpr he
    have h1 := Subgroup.smul_mem_pointwise_smul (⟨e, hEM he⟩ : M) (MulAut.conj m) _ hx
    rw [hmS, hP₂] at h1
    have h2 : (m : G) * e * (m : G)⁻¹ ∈ E' := Subgroup.mem_subgroupOf.mp h1
    obtain ⟨x, hxE, hx'⟩ := h2
    exact ⟨x, hxE, hx'⟩
  have hn : ρ'⁻¹ * (m : G) ∈ Subgroup.normalizer (E : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun e he => ?_
    obtain ⟨x, hxE, hx⟩ := hmE e he
    have : ρ'⁻¹ * (m : G) * e * (ρ'⁻¹ * (m : G))⁻¹ = x := by
      calc ρ'⁻¹ * (m : G) * e * (ρ'⁻¹ * (m : G))⁻¹ = ρ'⁻¹ * ((m : G) * e * (m : G)⁻¹) * ρ' := by
            group
        _ = ρ'⁻¹ * (ρ' * x * ρ'⁻¹) * ρ' := by rw [hx]
        _ = x := by group
    rw [this]
    exact hxE
  have hmM : (m : G) ∈ Θ ⊔ E := by
    rw [sup_comm]
    exact m.2
  obtain ⟨w, hw, e', he', hme⟩ := exists_mul_of_mem_sup hEΘ hmM
  set ρ₂ : G := w⁻¹ * ρ' with hρ₂
  have hρ₂E : ρ₂ ∈ Subgroup.normalizer (E : Set G) := by
    have h1 : ρ₂ = e' * (ρ'⁻¹ * (m : G))⁻¹ := by
      rw [hρ₂, hme]
      group
    rw [h1]
    exact mul_mem (Subgroup.le_normalizer he') (inv_mem hn)
  have hρ'₂ : ρ'⁻¹ * ρ₂ ∈ Θ := by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hρΘ) w⁻¹).mp (inv_mem hw)
    rw [hρ₂]
    simpa [mul_assoc] using h
  have hρΘ' : ∀ u ∈ Θ, ρ' * u * ρ'⁻¹ ∈ Θ := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hρΘ u).mp hu
  have hz : ρ₂ ^ 3 ∈ Θ := by
    have e : ρ₂ ^ 3 = w⁻¹ * (ρ' * w⁻¹ * ρ'⁻¹) * (ρ' * (ρ' * w⁻¹ * ρ'⁻¹) * ρ'⁻¹) * ρ' ^ 3 := by
      rw [pow_three', pow_three' ρ', hρ₂]
      group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (inv_mem hw) (hρΘ' _ (inv_mem hw)))
      (hρΘ' _ (hρΘ' _ (inv_mem hw)))) hρ3
  set z : G := ρ₂ ^ 3 with hzdef
  have hr : orderOf z ∣ Nat.card Θ := Subgroup.orderOf_dvd_natCard Θ hz
  have hr3 : ¬ 3 ∣ orderOf z := fun h => hΘ3 (h.trans hr)
  have hco : Nat.Coprime (orderOf z) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hr3).symm
  obtain ⟨k, hk0, hk1⟩ := Nat.chineseRemainder hco 0 1
  have hk0' : orderOf z ∣ k := Nat.modEq_zero_iff_dvd.mp hk0
  have hk1' : k % 3 = 1 := by simpa [Nat.ModEq] using hk1
  obtain ⟨j, hj⟩ : ∃ j, k = 3 * j + 1 := ⟨k / 3, by omega⟩
  refine ⟨ρ₂ ^ k, ?_, ?_, ?_⟩
  · have : ρ₂ ^ k = ρ₂ * z ^ j := by
      rw [hj, hzdef, ← pow_mul, ← pow_succ']
    rw [this]
    have h1 : z ^ j ∈ Θ := pow_mem hz j
    have h2 : ρ'⁻¹ * (ρ₂ * z ^ j) = (ρ'⁻¹ * ρ₂) * z ^ j := (mul_assoc _ _ _).symm
    rw [h2]
    exact mul_mem hρ'₂ h1
  · rw [pow_right_comm, ← hzdef]
    exact orderOf_dvd_iff_pow_eq_one.mp hk0'
  · exact pow_mem hρ₂E k

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
