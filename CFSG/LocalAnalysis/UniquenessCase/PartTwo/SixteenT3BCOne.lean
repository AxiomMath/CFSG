module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3BCPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Ctx
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Star
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Image
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Main
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3OddNc
import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofTypesTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_exists_noncyclic_cent_of_case168_1 (D : Data G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Hyp151 D ⊥ V L) (h1 : Case168_1 D ⊥ V hV L) :
    ∃ B : Subgroup G, B ≤ D.M ∧ IsPGroup 3 B ∧ ¬ IsCyclic B ∧
      ∀ b ∈ B, ∀ u ∈ v1Sub D.M ⊥ V hV L, b * u = u * b := by
  obtain ⟨-, ⟨eL⟩, -, -⟩ := h1
  obtain ⟨E, hE, hcard⟩ :=
    CFSG.RankThree.PartTwo.Sec15.Proof153Twin2.exists_e9_alternatingGroup_six
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₀, hE₀L, hE₀el, hE₀card⟩ : ∃ E₀ : Subgroup (MulAut (Vtil ⊥ V hV)),
      E₀ ≤ barSub ⊥ V hV L ∧ IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 9 :=
    ⟨(E.map eL.symm.toMonoidHom).map (lBar ⊥ V hV L).subtype, Subgroup.map_subtype_le _,
      (hE.map _).map _, by
        rw [Subgroup.card_map_of_injective (lBar ⊥ V hV L).subtype_injective,
          Subgroup.card_map_of_injective eL.symm.injective, hcard]⟩
  obtain ⟨Y, hYL, hYp, hYc⟩ := c8_exists_noncyclic_le_of_le_barSub (p := 3) hE₀L
    hE₀el.isPGroup (s16c7_not_isCyclic_of_elemAbelian Nat.prime_three hE₀el (by omega))
  exact ⟨Y, hYL.trans hS.le, hYp, hYc, fun b hb u hu =>
    Sixteen21.commute_of_mem_v1Sub hV hS rfl (hYL hb) hu⟩

theorem s16t_barSub_eq_bot_of_gammaSet_of_case168_1 (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h111 : W3Thm111 G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV) (hk : D.k = 1) (ha : aBar D.M ⊥ V hV < 2)
    (hm : 3 ≤ mBar D.M ⊥ V hV) {A : Subgroup G} (hA : A ∈ E3.gammaSet V D.k D.T) :
    barSub ⊥ V hV A = ⊥ := by
  obtain ⟨hAT, g, hAg, hAq⟩ := hA
  have hP := hc.setting.hyp16.hyp125.pairFacts
  have hMst : D.M ≤ stabTil ⊥ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hAst : A ≤ stabTil ⊥ V := hAM.trans hMst
  have hVel : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hAel : IsElemAbelian 2 A := hVel.mono hAg
  by_contra hne
  have hs : E3.sParam hVel = mBar D.M ⊥ V hV := by
    rw [E3.sParam_conj hV g hVel]
    exact s16c167_sParam_eq_mBar D hx h61 h111 hc.setting.hyp16 (by omega)
  have hhyp : ∀ B : Subgroup G, B ≤ A → E3.mQuot A B = 1 →
      V ⊓ centralizer (B : Set G) = V ⊓ centralizer (A : Set G) := by
    intro B hBA hB1
    have hlt : E3.mQuot (conjSubgroup V g) B < E3.sParam hVel := by
      rw [E3.mQuot_add hBA hAg, hB1, hAq, hk, hs]
      omega
    exact (E3.e3_6 hVel hBA hAg hlt (B2F.isPGroup_of_isElemAbelian hV)).1.symm
  have hmem : barSub ⊥ V hV A ∈ calABar 2 D.M ⊥ V hV :=
    s16c167_barSub_mem_calABar_of_hyperplanes hV rfl hAM hAst hAel hne hhyp
  have h2 : 2 ≤ aBar D.M ⊥ V hV := E3.le_aParam_of_mem_aSet (by norm_num) hmem
  omega

theorem s16t_insp_of_case168_1 (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h111 : W3Thm111 G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M)
    (hc : Counterex16 D ⊥ V L hV) (h1 : Case168_1 D ⊥ V hV L) : Insp1613U D V := by
  have h125 : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hP := h125.pairFacts
  have h3σ : 3 ∈ D.sig := by
    rw [h1.2.2.2]
    exact Set.mem_singleton 3
  have hk : D.k = 1 := Data.k_eq_one_of_three_mem D hSg h1219 h3σ
  obtain ⟨B, hBM, hBp, hBc, hBV₁⟩ :=
    s16t_exists_noncyclic_cent_of_case168_1 D hc.setting.hyp151 h1
  have hv : v1Sub D.M ⊥ V hV L = ⊥ :=
    s16e_v1Sub_eq_bot_of_noncyclic D h61 h125 hV h3σ hBM hBp hBc hBV₁ hC
  obtain ⟨ha, hm⟩ := s16t_aBar_lt_two_and_three_le_mBar_of_case168_1 D hc h1 hv
  have hM0 : D.M ≤ normalizer (⊥ : Subgroup G) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp
  have hAV : ∀ A ∈ E3.gammaSet V D.k D.T, A ≤ centralizer (V : Set G) := by
    intro A hA
    have hbot := s16t_barSub_eq_bot_of_gammaSet_of_case168_1 D hx h61 h111 hc hk ha hm hA
    have hAM : A ≤ D.M := hA.1.trans D.sylowM.le
    have := (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV hP.le_normalizer hM0 hAM).1 hbot
    rw [UC22.cTilde_bot D.M V] at this
    exact fun a ha => (Subgroup.mem_inf.1 (this ha)).2
  have hWV : E3.wClos V D.k D.T ≤ centralizer (V : Set G) := iSup₂_le hAV
  have hVW : V ≤ centralizer (E3.wClos V D.k D.T : Set G) :=
    Subgroup.le_centralizer_iff.1 hWV
  refine ⟨V ⊓ centralizer (E3.wClos V D.k D.T : Set G), s16c167_fixV_wClos_ne_bot D h125,
    le_rfl, 3, h3σ, B, le_inf hBM ?_, hBp, hBc⟩
  rw [inf_eq_left.2 hVW]
  exact (hBM.trans hP.le_normalizer)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
