module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.MultSpaceRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.MultSpaceBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin

private theorem apply_eq_of_card_eq_two {W : Type} [CommGroup W] {U : Subgroup W}
    (hU : Nat.card ↥U = 2) {m : MulAut W} (hm : m ∈ stabSub U) {u : W} (hu : u ∈ U) :
    m u = u := by
  by_cases hu1 : u = 1
  · rw [hu1, map_one]
  obtain ⟨v, -, hv⟩ := (Nat.card_eq_two_iff' (1 : ↥U)).mp hU
  have e1 := hv ⟨u, hu⟩ fun h => hu1 (congrArg Subtype.val h)
  have e2 := hv ⟨m u, (mem_stabSub.mp hm u).mpr hu⟩ fun h =>
    hu1 ((MulEquiv.map_eq_one_iff m).mp (congrArg Subtype.val h))
  exact congrArg Subtype.val (e2.trans e1.symm)

theorem k141MultSpace_holds : K141MultSpace := by
  intro W _ _ hW Y L M hL3 _ hM hY hfix htr hbasic hm
  by_cases hM1 : M = ⊥
  · exact Or.inl hM1
  obtain ⟨T, hTL, hT⟩ := MultSpace.exists_le_forall_card_inf_fixV_eq_two hW hL3 hfix
  have hMc : M ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [hM]
    exact inf_le_right
  have hstab : M ≤ stabSub (fixV T) :=
    MultSpace.le_stabSub_fixV (hMc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTL)))
  have hfaith : ∀ m ∈ M, (∀ u ∈ fixV T, m u = u) → m = 1 := fun m hm hmT =>
    MultSpace.eq_one_of_mem_centralizer_of_forall_fixV hfix htr.1 hT (hMc hm) hmT
  rcases MultSpace.rk_eq_three_and_card_fixV_or hW hL3 hM hY hfix htr hm hTL hT with
    ⟨h3, h16⟩ | h2
  · refine Or.inr ⟨fixV T, h16, hstab, eq_bot_iff.mpr fun m hm => ?_,
      MultSpace.isBasicModule_autSub hW hL3 hM hY hfix htr hbasic hTL hT h3 h16 hM1⟩
    exact Subgroup.mem_bot.mpr (hfaith m hm.1 (mem_centSub.mp hm.2))
  · exact absurd (eq_bot_iff.mpr fun m hm => Subgroup.mem_bot.mpr
      (hfaith m hm fun u hu => apply_eq_of_card_eq_two h2 (hstab hm) hu)) hM1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
