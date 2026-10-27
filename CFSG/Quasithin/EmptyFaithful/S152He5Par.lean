module

public import CFSG.Quasithin.EmptyFaithful.S152He5Aut
public import CFSG.Quasithin.EmptyFaithful.S152He4Par
public import CFSG.Quasithin.EmptyFaithful.S152He4Quot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.He5
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem overBool2_of_goodShape {G : Type} [Group G] [Finite G] {X T : Subgroup G}
    (hT : IsSylowTwoOf T X) (hgood : GoodShape152 X) : OverBool2 (imageOTwoQuot X T) := by
  have hS := CFSG.Quasithin.He4.isSylowTwoOf_imageOTwoQuot_top hT
  have hp : IsPGroup 2 (imageOTwoQuot X T) := hS.2.1
  have hi : ¬ 2 ∣ (imageOTwoQuot X T).index := by
    have h := hS.2.2
    change ¬ 2 ∣ (imageOTwoQuot X T).relIndex ⊤ at h
    rwa [Subgroup.relIndex_top_right] at h
  rcases hgood with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · let e' : OTwoQuot X ≃* MulAut (projectiveSL n K2) :=
      e.trans (MulAut.congr (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K2))
    have hQ : IsPGroup 2 ((imageOTwoQuot X T).map e'.toMonoidHom) := hp.map e'.toMonoidHom
    have hQi : ¬ 2 ∣ ((imageOTwoQuot X T).map e'.toMonoidHom).index := by
      have := Subgroup.index_map_equiv (H := imageOTwoQuot X T) e'
      exact this ▸ hi
    have hO : OverBool2 ((imageOTwoQuot X T).map e'.toMonoidHom) := by
      rcases hn with rfl | rfl
      · exact overBool2_mulAut_four hQ hQi
      · exact overBool2_mulAut_five hQ hQi
    exact OverBool2.sylow_of_mulEquiv e'.symm hQ hQi hO hp hi
  · have hQ : IsPGroup 2 ((imageOTwoQuot X T).map e.toMonoidHom) := hp.map e.toMonoidHom
    have hQi : ¬ 2 ∣ ((imageOTwoQuot X T).map e.toMonoidHom).index := by
      have := Subgroup.index_map_equiv (H := imageOTwoQuot X T) e
      exact this ▸ hi
    exact OverBool2.sylow_of_mulEquiv e.symm hQ hQi (overBool2_l32WrZ2 hQ hQi) hp hi

theorem insp15227ParGood_holds : Insp15227ParGood := by
  intro G _ _ T Mc M H hs hH hV hcase hgood P hP hPM
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hTM : T ≤ M := hs.mf.1.1.2
  have hXMc : conjClosure (oTwoUpper H) Mc ⊔ T ≤ Mc := sup_le (le_Mc_of_case hTMc hcase) hTMc
  have hMc : pCoreOf 2 Mc ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hs.qtfe.mc_max.1
  have hTX : T ≤ conjClosure (oTwoUpper H) Mc ⊔ T := le_sup_right
  have hsylX : IsSylowTwoOf T (conjClosure (oTwoUpper H) Mc ⊔ T) :=
    isSylowTwoOf_of_le151 hs.qtfe.sylow hTX
  have hmaxP : IsMaxSubgroupIn P T :=
    isMaxSubgroupIn_of_overBool2 hsylX (overBool2_of_goodShape hsylX hgood) P hP
  refine isHStar_of_uFamHat_of_max_le hs.qtfe.sylow hXMc hTMc hMc hP hPM fun N hN hTN => ?_
  have hNT : N = T := by
    by_contra hne
    exact hN.1.ne (hmaxP.2 N (lt_of_le_of_ne hTN (Ne.symm hne)) hN.1.le)
  rw [hNT]
  exact hTM

end CFSG.Quasithin
