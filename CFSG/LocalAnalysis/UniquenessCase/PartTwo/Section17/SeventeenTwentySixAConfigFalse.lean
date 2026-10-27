module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.GapNEHolds
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASTwelve
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixAIsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixAOddTransp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixAFirst
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixAAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W3Lem71Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2CentralizerHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFactHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem config17_26a_II_not_le_pCoreOf_sup {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hAO : ¬ A ≤ pCoreOf 2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian)) :
    ¬ A ≤ pCoreOf 2 (L ⊔ D.T) := by
  intro hAle
  have hAH1 : A ≤ H17_25_one D V₀ V L c.hyp125.isElemAbelian :=
    hA.1.trans (T_le_H17_25_one c.hyp125)
  have hH1 : H17_25_one D V₀ V L c.hyp125.isElemAbelian ≤ L ⊔ D.T := by
    change preBarSub (L ⊔ D.T) V₀ V c.hyp125.isElemAbelian _ ≤ L ⊔ D.T
    exact inf_le_left
  exact hAO ((le_inf hAH1 hAle).trans (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hH1))

theorem config17_26a_II_relIndex
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h20 : R17_20At D V₀ V) (hC117 : C117 D V₀ V) (hJ2 : IsSpor (Bar2 L) .J2)
    (hm : 4 < mSub V₀) {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) {h : G}
    (hO1 : InCalO 1 (normalizer (A : Set G)) ⊥ A h)
    (hker : (A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h)).subgroupOf (L ⊔ D.T) ≤
      (gap17_25_action c.hyp125 c).ker) :
    ((gap17_25_action c.hyp125 c).ker.map (L ⊔ D.T).subtype).relIndex A ≤ 2 ∧
      (pCoreOf 2 (L ⊔ D.T)).relIndex A ≤ 2 := by
  classical
  have hV := c.hyp125.isElemAbelian
  obtain ⟨hAel, hATI, hrk, hAT⟩ := config17_26a_II_gammaSet_facts c.hyp125 hA hm
  have h2rk : 2 < rk ↥A := by rw [hrk]; omega
  set H : Subgroup G := L ⊔ D.T with hH
  set B : Subgroup G := A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h) with hB
  have hBeq : B = nVSub A h := by
    rw [hB]
    exact inf_pCoreOf_sup_conj_eq hAel hATI h2rk hO1
  have hBrel : B.relIndex A = 2 := by
    rw [hBeq, E3.relIndex_eq_two_pow
      (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hAel),
      mQuot_nVSub_eq_one hAel hO1]
    norm_num
  have hAH : A ≤ H := hAT.trans le_sup_right
  have hBH : B ≤ H := inf_le_left.trans hAH
  have hBle : B ≤ (gap17_25_action c.hyp125 c).ker.map H.subtype := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hBH hx⟩, hker (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hdvd1 : ((gap17_25_action c.hyp125 c).ker.map H.subtype).relIndex A ∣ 2 := by
    have hdvd := Subgroup.relIndex_dvd_of_le_left A hBle
    rwa [hBrel] at hdvd
  have hkerle : (gap17_25_action c.hyp125 c).ker.map H.subtype ≤ pCoreOf 2 H := by
    have hMnorm : D.M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 (h20 L c).2.1
    have hsimple : IsSimpleGroup (Bar2 L) := by
      obtain ⟨e⟩ := hJ2
      exact (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
    have hL1 : barSub V₀ V hV L ≠ ⊥ := gap17_25_barSub_L_ne_bot c h20 hC117
    have hp : IsPGroup 2 (gap17_25_action c.hyp125 c).ker :=
      gap17_25_action_ker_isPGroup c.hyp125 c hMnorm hsimple hL1
    exact Subgroup.map_mono
      (CFSG.LieType.BorelTits.le_pCore 2 (gap17_25_action c.hyp125 c).normal_ker hp)
  have hdvd2 : (pCoreOf 2 H).relIndex A ∣ 2 :=
    (Subgroup.relIndex_dvd_of_le_left A hkerle).trans hdvd1
  exact ⟨Nat.le_of_dvd (by norm_num) hdvd1, Nat.le_of_dvd (by norm_num) hdvd2⟩

theorem false_of_config17_26a_II
    {D : Data G} {V₀ V : Subgroup G} (h20 : R17_20At D V₀ V) (h23 : R17_23At D V₀ V)
    (hC117 : C117 D V₀ V) (hK2 : K_J2_centralizer_shape)
    (hKF1 : Inputs1719.K_J2_centralizer_fpf) (hKF2 : Inputs1719.K_J2_involution_product) :
    ¬ Config17_26a_II D V₀ V := by
  rintro ⟨L, c, hm, -, h2grp, A, hA, hAO, h, hh, hO1, hB, -⟩
  have hJ2 : IsSpor (Bar2 L) .J2 := h23 L c
  have hker := config17_26a_II_inf_le_ker c h20 hC117 hKF1 hJ2 hm hA hh hO1 hB
  have hAO' := config17_26a_II_not_le_pCoreOf_sup c hA hAO
  obtain ⟨hAk, hAO2⟩ := config17_26a_II_relIndex c h20 hC117 hJ2 hm hA hO1 hker
  have hE := config17_26a_II_isE c h20 hC117 hJ2 hA hAO' hAk
  have hZ := config17_26a_II_center_ne_bot c h20 hC117 hK2 hJ2 hm h2grp hA hE
  exact config17_26a_II_false_of_center c h20 hC117 hKF2 hJ2 hA hAO' hAO2 hZ

theorem seventeen_twentysix_a_of_KF
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    {D : Data G} {V₀ V : Subgroup G} (h20 : R17_20At D V₀ V) (h22 : R17_22At D V₀ V)
    (h23 : R17_23At D V₀ V) (h25 : R17_25At D V₀ V) (hSg : UC6S846.SigmaStd D)
    (h880 : F08.R880 D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D)
    (h88 : W3Thm88 G) (h861 : W3Lem86_1 G)
    (h93 : ∀ L, Ctx17_17 D V₀ V L → CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T)
    (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    (hC117 : C117 D V₀ V) :
    R17_26aAt D V₀ V := by
  have hJ2aut : K_J2_aut_five_rank := k_J2_aut_five_rank_holds
  have hJ2center : K_J2_center_five := k_J2_center_five_holds
  have hK2 : K_J2_centralizer_shape := k_J2_centralizer_shape_holds
  have hK3 : Inputs1719.K_J2_threeCentral := Inputs1719.k_J2_threeCentral_holds
  have hKF1 : Inputs1719.K_J2_centralizer_fpf :=
    Inputs1719.k_J2_centralizer_fpf_holds
  have hKF2 : Inputs1719.K_J2_involution_product :=
    Inputs1719.k_J2_involution_product_holds
  exact (seventeen_twentysix_a_reduction_of_U hTim hcat h20 h22 h23 h25 hSg h880 hJ2aut h61
    h66 h88
    (r126_of_twelve_six_AS D h5_11 h5_13 h66) h861 h93
    (fun H₀ => gap17_26_NE_holds D V₀ V H₀ h5_11 h5_13 h66 h861 hTim hcat)
    hJ2center hC117 hK2 hK3
    (gap17_26a_Alt_holds hTim h20 h22 h23 hSg h66 h88 h93 hC117 hK2 hK3)
    (gap17_26a_First_holds w3Lem71_holds hK2)).resolve_right
    (false_of_config17_26a_II h20 h23 hC117 hK2 hKF1 hKF2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
