module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H30
public import CFSG.Quasithin.Vol2.Ch10SecQ9H40

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

theorem mem_X14_of {g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)}
    (h1 : PresStd (m := 1) (k := 4) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (h4 : PresStd (m := 4) (k := 1) (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) : g ∈ X14 := ⟨h1, h4⟩

theorem normalizer_X14 :
    Subgroup.normalizer (X14 : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) = X14 := by
  refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
  have hfix : ∀ v ∈ fixN X14, v ∈ stdE (1 + 4) 1 := by
    intro v hv i hi
    have key : ∀ (j : Fin 5) (h : (0 : Fin 5) ≠ j), trvE 0 j h ∈ X14 → v j = 0 := by
      intro j h ht
      have h1 := congrFun (hv _ ht) 0
      rw [trvE_mulVec] at h1
      simpa using h1
    fin_cases i
    · exact absurd hi (by decide)
    · exact key 1 (by decide) (mem_X14_of (by unfold PresStd; decide) (by unfold PresStd; decide))
    · exact key 2 (by decide) (mem_X14_of (by unfold PresStd; decide) (by unfold PresStd; decide))
    · exact key 3 (by decide) (mem_X14_of (by unfold PresStd; decide) (by unfold PresStd; decide))
    · exact key 4 (by decide) (mem_X14_of (by unfold PresStd; decide) (by unfold PresStd; decide))
  have he0 : ∀ v ∈ stdE (1 + 4) 1, v ∈ fixN X14 := fun v hv x hx =>
    smul_eq_of_topB_one (m := 1) (k := 4) hx.1 (topB_eq_one_of_one (k := 4) ⟨x, hx.1⟩) hv
  have hg1 : PresStd (m := 1) (k := 4) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) :=
    presStd_of_smul_mem fun j => hfix _ (smul_mem_fixN hg (he0 _ (castAdd_mem_stdE j)))
  have hg4 : PresStd (m := 4) (k := 1) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
    refine presStd_of_smul_mem fun j => ?_
    have key : ∀ (h : Fin.castAdd 1 j ≠ (4 : Fin 5)), trvE (Fin.castAdd 1 j) 4 h ∈ X14 →
        g • Pi.single (Fin.castAdd 1 j) (1 : ZMod 2) ∈ stdE (4 + 1) 4 := by
      intro h ht
      have hz : g * trvE (Fin.castAdd 1 j) 4 h * g⁻¹ ∈ X14 :=
        (Subgroup.mem_normalizer_iff.mp hg _).mp ht
      obtain ⟨w, hw⟩ : ∃ w : Fin 5 → ZMod 2, w = Pi.single 4 1 := ⟨_, rfl⟩
      have he : Pi.single (Fin.castAdd 1 j) (1 : ZMod 2) = trvE (Fin.castAdd 1 j) 4 h • w + w := by
        rw [hw, trvE_mulVec, Pi.single_eq_same, one_smul, add_add_cancel_vec]
      rw [he, smul_add, show g • trvE (Fin.castAdd 1 j) 4 h • w =
        (g * trvE (Fin.castAdd 1 j) 4 h * g⁻¹) • g • w by
          rw [smul_smul, smul_smul, inv_mul_cancel_right]]
      exact smul_add_mem_of_botB_one (m := 4) (k := 1) hz.2 (botB_eq_one_of_one ⟨_, hz.2⟩) _
    fin_cases j
    · exact key (by decide) (mem_X14_of (by unfold PresStd; decide) (by unfold PresStd; decide))
    · exact key (by decide) (mem_X14_of (by unfold PresStd; decide) (by unfold PresStd; decide))
    · exact key (by decide) (mem_X14_of (by unfold PresStd; decide) (by unfold PresStd; decide))
    · exact key (by decide) (mem_X14_of (by unfold PresStd; decide) (by unfold PresStd; decide))
  exact ⟨hg1, hg4⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
