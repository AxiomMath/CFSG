module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenSwap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenXT
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiagR42
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexNormalHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.DeltaPrimePullback
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzAutRankHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4DeltaHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U5DeltaHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SwapSp4InFHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified

theorem nOf_eq_of_isU3 {L : Subgroup G} {n : ℕ} (h : IsU3 (Bar2 L) n) : S17.nOf L = n :=
  S17.nOf_eq_of_isChar2LieShape h (Or.inr (Or.inl ⟨rfl, rfl⟩))

end Certified

theorem r18_7b
    {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h126 : R126 D) (h111 : W3Thm111 G) (hSg : UC6S846.SigmaStd D)
    (h1766 : S17.R17_66_1At D V₀ V) (h184 : R18_4At D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) (h1767 : S17.R17_67At D V₀ V)
    (h43c : W3Lem45_2Chief) :
    R18_7bAt D V₀ V p L h := by
  classical
  have hKSp4 : Inputs1719.K_SwapSp4InF := Inputs1719.k_SwapSp4InF_holds
  have hKU4 : Inputs1719.KU4Delta := Inputs1719.kU4Delta_holds
  have hKU5 : Inputs1719.KU5Delta := Inputs1719.kU5Delta_holds
  have hKU3 : Inputs1719.K_U3IndexNormal := Inputs1719.k_U3IndexNormal_holds
  have hKL2 : Inputs1719.K_L2SzAutRank := Inputs1719.k_L2SzAutRank_holds
  have hUL : UniqueMax D.M L := by
    rcases h1766 p h.hp L h.hL (UC22.conjClosure D.M L) rfl h.hX with hh | hh
    · exact hh
    · exact absurd hh h184
  have hcard : Nat.card V₀ ≤ 2 :=
    (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).mp h.small
  have hL1 : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥ :=
    barSub_ne_bot_of_card_le_two D h127 h.hyp125 h.hL.1 hUL hcard
  have hX1 : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥ :=
    TwelveTwentyThree.barSub_conjClosure_ne_bot h.hyp125.isElemAbelian hL1
  by_cases hV₀ : V₀ = ⊥
  · exact r18_7b_of_bot hx h61 h126 h111 h hV₀ hL1 h1766 h184
  · rcases h1767 hV₀ p h.hp L h.hL (UC22.conjClosure D.M L) rfl h.hX with
      hU5 | ⟨n, -, hU4⟩ | ⟨n, hSp4, hSwap⟩ | ⟨hXne, -, -⟩ | ⟨n, -, hshape5⟩
    · exact r18_7b_U5 h hx h61 h127 h1114 h162 hTor h1482 h126 hSg h1742 hKU5 hKU3 hV₀ hX1 hU5
    · exact r18_7b_U4 h hx h61 h127 h1114 h162 hTor h1482 h126 hSg h1742 hKU4 hKL2 hV₀
        hX1 hU4
    ·
      have hsX : IsSimpleGroup (Bar2 (UC22.conjClosure D.M L)) :=
        LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp4
      have hXL : UC22.conjClosure D.M L = L :=
        conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hsX
      have hSpL : IsSp4 (Bar2 L) n := hXL ▸ hSp4
      have hnof : S17.nOf L = n := S17.nOf_eq_of_isSp4 hSpL
      have hSp : IsSp4 (Bar2 (UC22.conjClosure D.M L)) (S17.nOf L) := by
        rw [hXL, hnof]
        exact hSpL
      exact r18_7b_of_ne_bot_XT_sp4 h hx h61 h127 h1114 h162 hTor h1482 h126 hSg hV₀ hX1
        h1766 h184 hKSp4 hSp hSwap
    ·
      exact r18_7b_of_ne_bot_XT_diag' h hx h61 h127 h1114 h162 hTor h1482 h126 hSg hV₀ hX1
        h1766 h184 h43c hKL2 h1742 hXne
    ·
      rcases hshape5 with hL2 | hU3s
      · have hsX : IsSimpleGroup (Bar2 (UC22.conjClosure D.M L)) :=
          LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
        have hXL : UC22.conjClosure D.M L = L :=
          conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hsX
        have hL2L : IsL2 (Bar2 L) n := hXL ▸ hL2
        have hL2' : IsL2 (Bar2 L) (S17.nOf L) := by
          rw [S17.nOf_eq_of_isL2 hL2L]
          exact hL2L
        exact r18_7b_of_ne_bot_XT_l2 h hx h61 h127 h1114 h162 hTor h1482 h126 hSg hV₀ hX1
          h1766 h184 hKL2 hXL hL2'
      · have hsX : IsSimpleGroup (Bar2 (UC22.conjClosure D.M L)) :=
          LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3s
        have hXL : UC22.conjClosure D.M L = L :=
          conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hsX
        have hU3L : IsU3 (Bar2 L) n := hXL ▸ hU3s
        have hU3' : IsU3 (Bar2 L) (S17.nOf L) := by
          rw [nOf_eq_of_isU3 hU3L]
          exact hU3L
        exact r18_7b_of_ne_bot_XT_u3 h hx h61 h127 h1114 h162 hTor h1482 h126 hSg hV₀ hX1
          h1766 h184 hKU3 hXL hU3'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
