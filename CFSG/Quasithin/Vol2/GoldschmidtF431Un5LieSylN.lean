module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylM

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem syl_sY_le_cent : sylSY h ≤ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, t5Y, ← map_mul, ← map_mul]
  have hz : z₂SU h ∈ Vsub h := vSU_mem_Vsub (isHerm_swap h)
  rw [(commute_Vsub_iff (Ssub_le_Usub hs)).2 hs _ hz]

theorem syl_lY_le_cent : lY h ≤ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) := by
  have hch : CharP K 2 := h.charP
  rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, t5Y, ← map_mul, ← map_mul]
  rw [mul_inv_eq_iff_eq_mul.1 (levHom_conj_z₂SU B)]

theorem syl_cent_eq_sup
    (H1 : ∀ x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)),
      ∃ B : SpecialLinearGroup (Fin 2) h.fixedField, ∃ s ∈ Ssub h,
        x = hypProj h 2 1 (levHom h B * s)) :
    Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) = sylSY h ⊔ lY h := by
  refine le_antisymm (fun x hx => ?_) (sup_le syl_sY_le_cent syl_lY_le_cent)
  obtain ⟨B, s, hs, rfl⟩ := H1 x hx
  rw [map_mul]
  exact mul_mem (Subgroup.mem_sup_right ⟨levHom h B, ⟨B, rfl⟩, rfl⟩)
    (Subgroup.mem_sup_left ⟨s, hs, rfl⟩)

theorem syl_card_cent
    (H1 : ∀ x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)),
      ∃ B : SpecialLinearGroup (Fin 2) h.fixedField, ∃ s ∈ Ssub h,
        x = hypProj h 2 1 (levHom h B * s)) :
    Nat.card (Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))) =
      (2 ^ f) ^ 8 * (2 ^ f * ((2 ^ f) ^ 2 - 1)) := by
  rw [syl_cent_eq_sup H1, syl_card_sup_lY]

end CFSG.Quasithin.H13.F431.Un.L5
