module

public import CFSG.RankThree.PartTwo.Sec21.FF84S47
public import CFSG.RankThree.PartTwo.Sec21.FF84S3A10

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s Eo core_Y cc_mem_Eo dd_mem_Eo m1_eq m2_eq m₁ m₂
  Eo_le_nor Ua_nor_cc Ua_nor_dd Ub_nor_cc Ub_nor_dd)

theorem Eo_eq_Pm : Eo = Pm := by
  refine le_antisymm ?_ ?_
  · show Subgroup.closure ({m₁, m₂} : Set P8) ≤ Pm
    refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 ?_⟩)
    · rw [m1_eq]
      exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    · rw [m2_eq]
      exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
        (mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  · show Subgroup.closure ({cc, dd} : Set P8) ≤ Eo
    exact (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨cc_mem_Eo, Set.singleton_subset_iff.2 dd_mem_Eo⟩)

theorem swap_mul_swap_mem_A8 {a b c d : Fin 8} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ A8s := by
  show _ ∈ alternatingGroup (Fin 8)
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hcd]
  norm_num

theorem v4_le_A8 {a b c d : Fin 8} (h1 : a ≠ b) (h2 : c ≠ d) (h3 : a ≠ c) (h4 : b ≠ d) :
    v4 a b c d ≤ A8s := by
  show Subgroup.closure _ ≤ A8s
  refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 ?_⟩)
  · exact swap_mul_swap_mem_A8 h1 h2
  · exact swap_mul_swap_mem_A8 h3 h4

theorem Ua_le_A8 : Ua ≤ A8s := by
  show v4 3 4 5 6 ⊔ v4 0 1 2 7 ≤ A8s
  exact sup_le (v4_le_A8 (by decide) (by decide) (by decide) (by decide))
    (v4_le_A8 (by decide) (by decide) (by decide) (by decide))

theorem Ub_le_A8 : Ub ≤ A8s := by
  show v4 3 4 5 7 ⊔ v4 0 1 2 6 ≤ A8s
  exact sup_le (v4_le_A8 (by decide) (by decide) (by decide) (by decide))
    (v4_le_A8 (by decide) (by decide) (by decide) (by decide))

theorem Ua_isPGroup : IsPGroup 2 Ua := IsPGroup.of_card (n := 4) (by rw [Ua_card]; norm_num)

theorem Ub_isPGroup : IsPGroup 2 Ub := IsPGroup.of_card (n := 4) (by rw [Ub_card]; norm_num)

theorem Pm_le_nor_Ua : Pm ≤ Subgroup.normalizer (Ua : Set P8) := by
  rw [← Eo_eq_Pm]
  exact Eo_le_nor Ua_nor_cc Ua_nor_dd

theorem Pm_le_nor_Ub : Pm ≤ Subgroup.normalizer (Ub : Set P8) := by
  rw [← Eo_eq_Pm]
  exact Eo_le_nor Ub_nor_cc Ub_nor_dd

theorem Ua_mem_pistar : Ua ∈ PiStar A8s Pm 2 := by
  refine ⟨Ua_le_A8, Ua_isPGroup, Pm_le_nor_Ua, fun V hUV hVA hV2 hVn => ?_⟩
  rcases core_Y V hVA hV2 (by rw [Eo_eq_Pm]; exact hVn) with h | h
  · exfalso
    have hUa0 : Ua = ⊥ := (inf_eq_left.2 (hUV.trans h)).symm.trans Ua_inf_Ub
    have hc := Ua_card
    rw [hUa0, Subgroup.card_bot] at hc
    norm_num at hc
  · exact le_antisymm h hUV

theorem Ub_mem_pistar : Ub ∈ PiStar A8s Pm 2 := by
  refine ⟨Ub_le_A8, Ub_isPGroup, Pm_le_nor_Ub, fun V hUV hVA hV2 hVn => ?_⟩
  rcases core_Y V hVA hV2 (by rw [Eo_eq_Pm]; exact hVn) with h | h
  · exact le_antisymm h hUV
  · exfalso
    have hUb0 : Ub = ⊥ := (inf_eq_left.2 (hUV.trans h)).symm.trans ((inf_comm _ _).trans Ua_inf_Ub)
    have hc := Ub_card
    rw [hUb0, Subgroup.card_bot] at hc
    norm_num at hc

theorem A_PiStar_holds : A_PiStar_stmt := by
  unfold A_PiStar_stmt
  ext U
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hUA, hU2, hUn, hmax⟩
    rcases core_Y U hUA hU2 (by rw [Eo_eq_Pm]; exact hUn) with h | h
    · exact Or.inr (hmax Ub h Ub_le_A8 Ub_isPGroup Pm_le_nor_Ub).symm
    · exact Or.inl (hmax Ua h Ua_le_A8 Ua_isPGroup Pm_le_nor_Ua).symm
  · rintro (rfl | rfl)
    · exact Ua_mem_pistar
    · exact Ub_mem_pistar

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
