module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3TIB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8UAB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_L_sup_le_cent_v1
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    L ⊔ conjSubgroup L x ≤
      Subgroup.centralizer
        ((v1Sub D.M ⊥ V h.hyp151.isElemAbelian L : Subgroup G) : Set G) := by
  have hv1 := s16h_e3_v1Sub_eq_sup_zx D h hs2 hxM hxn
  obtain ⟨hLc, hLxc⟩ := s16h_e3_cross_centralize D h hxM hxn
  have hZW : wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G) ≤
      wSub ⊥ V h.hyp151.isElemAbelian L := inf_le_left
  have hZC : wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer (L : Set G) := inf_le_right
  rw [hv1]
  refine sup_le ?_ ?_
  · refine Subgroup.le_centralizer_iff.2 (sup_le hZC ?_)
    exact (E3.conjSubgroup_mono_left x hZW).trans (Subgroup.le_centralizer_iff.1 hLc)
  · refine Subgroup.le_centralizer_iff.2 (sup_le ?_ ?_)
    · exact hZW.trans (Subgroup.le_centralizer_iff.1 hLxc)
    · rw [← E3.conjSubgroup_centralizer]
      exact E3.conjSubgroup_mono_left x hZC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
