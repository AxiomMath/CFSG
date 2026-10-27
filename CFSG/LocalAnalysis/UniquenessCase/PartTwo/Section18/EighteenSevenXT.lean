module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexNormal
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21j

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}

section Certified


theorem r18_7b_of_ne_bot_XT_u3 (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    (hV₀ : V₀ ≠ ⊥) (hX1 : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L)
    (hKidx : Inputs1719.K_U3IndexNormal) (hX : UC22.conjClosure D.M L = L)
    (hU3 : IsU3 (Bar2 L) (S17.nOf L)) :
    R18_7bAt D V₀ V p L h := by
  refine r18_7b_of_ne_bot_XT h hx h61 h127 h1114 h162 hTor h1482 h126 hSg hV₀ hX1
    h17_66_1 h18_4 ?_
  rw [hX]
  let H : Subgroup G := L ⊔ D.T
  have hLM : L ≤ D.M := h.hL.1.1.le
  have hHM : H ≤ D.M := sup_le hLM D.sylowM.le
  have hNM : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp
      (uc22p21j_normal_of_conjClosure_eq hLM hX.symm)
  have hNH : H ≤ Subgroup.normalizer (L : Set G) := hHM.trans hNM
  have hLnorm : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (show L ≤ H from le_sup_left)).mpr hNH
  have hsy : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D le_sup_right
  have hSU3 : IsSU3 (Bar2 L) (S17.nOf L) :=
    uc22p22d_isSU3_of_isU3 h.hL.1.2.2 hU3
  exact hKidx G L D.T H (S17.nOf L) le_sup_left hLnorm h.hL.1.2.1 h.hL.1.2.2 hSU3 hsy rfl

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
