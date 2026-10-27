module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open scoped commutatorElement
open CFSG.RankThree.PartTwo.KFacts (mul_mulAutConj_mul_inv)

variable {Y : Type} [Group Y] {Q : Type} [Group Q]

private theorem exists_subgroup_commute_inv (β : MulAut Y) {x : Y}
    (hCx : ∀ a b : Y, a * x = x * a → b * x = x * b → a * b = b * a) :
    ∃ I : Subgroup Y, ∀ w : Y, w ∈ I ↔ w * x = x * w ∧ β w = w⁻¹ := by
  refine ⟨{ carrier := {w | w * x = x * w ∧ β w = w⁻¹}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun w => Iff.rfl⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    have hac : Commute a x := ha
    have hbc : Commute b x := hb
    refine ⟨(hac.mul_left hbc).eq, ?_⟩
    rw [map_mul, ha', hb', hCx a b ha hb, mul_inv_rev]
  · exact ⟨by rw [one_mul, mul_one], by rw [map_one, inv_one]⟩
  · rintro a ⟨ha, ha'⟩
    have hac : Commute a x := ha
    exact ⟨hac.inv_left.eq, by rw [map_inv, ha']⟩

private theorem commute_and_inv_of_conj_commutator
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) {x : Y} {α β : MulAut Y}
    (hββ : β * β = 1) (hαx : α x = x) (hβx : β x = x) {w : Y}
    (hw : MulAut.conj w = α * β * α⁻¹ * β⁻¹) : w * x = x * w ∧ β w = w⁻¹ := by
  have hfix : ∀ γ : MulAut Y, γ x = x → γ⁻¹ x = x := fun γ h =>
    calc γ⁻¹ x = γ⁻¹ (γ x) := by rw [h]
      _ = x := MulAut.inv_apply_self Y γ x
  have hβi : β⁻¹ = β := inv_eq_of_mul_eq_one_right hββ
  have hβ2 : β⁻¹ * β⁻¹ = 1 := by rw [← mul_inv_rev, hββ, inv_one]
  refine ⟨?_, hinj ?_⟩
  · have h : MulAut.conj w x = x := by
      rw [hw]
      simp only [MulAut.mul_apply, hfix β hβx, hfix α hαx, hβx, hαx]
    rw [MulAut.conj_apply] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · rw [← mul_mulAutConj_mul_inv β w, map_inv, hw]
    calc β * (α * β * α⁻¹ * β⁻¹) * β⁻¹
        = β * α * β * α⁻¹ * (β⁻¹ * β⁻¹) := by group
      _ = β * α * β * α⁻¹ := by rw [hβ2, mul_one]
      _ = β * α * β⁻¹ * α⁻¹ := by rw [hβi]
      _ = (α * β * α⁻¹ * β⁻¹)⁻¹ := by group

theorem res1U3_exists_conj_of_mem_commutator (hZ : Subgroup.center Y = ⊥)
    (hI : ∀ σ τ : MulAut Y, CFSG.RankThree.PartTwo.KFacts.IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹))
    {x : Y} (hCx : ∀ a b : Y, a * x = x * a → b * x = x * b → a * b = b * a)
    (ρ : Q →* MulAut Y) {O : Subgroup Q} {z : Q} (hz2 : z ^ 2 = 1)
    (hOx : ∀ o ∈ O, ρ o x = x) (hzx : ρ z x = x) {j : Q}
    (hj : j ∈ ⁅O, Subgroup.zpowers z⁆) :
    ∃ w : Y, ρ j = MulAut.conj w ∧ w * x = x * w ∧ ρ z w = w⁻¹ := by
  obtain ⟨I, hIw⟩ := exists_subgroup_commute_inv (ρ z) hCx
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hcen : a ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := DFunLike.congr_fun ha g
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * a = a * g * a⁻¹ * a := by rw [h]
        _ = a * g := inv_mul_cancel_right _ _
    rw [hZ] at hcen
    exact Subgroup.mem_bot.mp hcen
  have hββ : ρ z * ρ z = 1 := by rw [← map_mul, ← pow_two, hz2, map_one]
  have hz2' : z ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hz2]
  have hcomm : ∀ o ∈ O, ρ ⁅o, z⁆ ∈ I.map MulAut.conj := by
    intro o ho
    obtain ⟨w, hw⟩ := hI (ρ o) (ρ z)
    obtain ⟨hwx, hwz⟩ := commute_and_inv_of_conj_commutator hinj hββ (hOx o ho) hzx hw
    refine Subgroup.mem_map.mpr ⟨w, (hIw w).2 ⟨hwx, hwz⟩, ?_⟩
    rw [hw]
    simp only [commutatorElement_def, map_mul, map_inv]
  have key : ⁅O, Subgroup.zpowers z⁆ ≤ (I.map MulAut.conj).comap ρ := by
    rw [Subgroup.commutator_le]
    intro o ho z' hz'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [zpow_mul, hz2', one_zpow, commutatorElement_one_right]
      exact one_mem _
    · rw [zpow_add, zpow_mul, hz2', one_zpow, one_mul, zpow_one]
      exact hcomm o ho
  obtain ⟨w, hw, hwj⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp (key hj))
  exact ⟨w, hwj.symm, (hIw w).1 hw⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
