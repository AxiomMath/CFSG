module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8UA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_v1Sub_eq_sup_zx (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    v1Sub D.M ⊥ V h.hyp151.isElemAbelian L =
      (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) ⊔
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) x := by
  rw [v1Sub_of_eq_bot D.M ⊥ _ _ L rfl]
  apply le_antisymm
  · refine iSup_le fun m => ?_
    rcases s16h_e3_conj_cent_cases D h hs2 hxM hxn m with hm | hm
    · rw [hm]
      exact le_sup_left
    · rw [hm]
      exact le_sup_right
  · refine sup_le ?_ ?_
    · refine le_trans ?_ (le_iSup (fun m : D.M =>
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G))
          (m : G)) 1)
      rw [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one]
    · exact le_iSup (fun m : D.M =>
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G))
          (m : G)) ⟨x, hxM⟩

theorem s16h_e3_sl28_v1_le_wsub_sup_zx (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    v1Sub D.M ⊥ V h.hyp151.isElemAbelian L ≤
      wSub ⊥ V h.hyp151.isElemAbelian L ⊔
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) x := by
  rw [s16h_e3_v1Sub_eq_sup_zx D h hs2 hxM hxn]
  exact sup_le_sup_right inf_le_left _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
