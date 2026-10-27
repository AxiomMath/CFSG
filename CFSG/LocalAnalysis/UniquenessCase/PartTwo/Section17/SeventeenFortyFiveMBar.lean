module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiagR42
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineSeven
public import CFSG.GroupTheory.TwoResidualOddOrder
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Mbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubNotNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixHyp
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubConjClosure
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s17_45_B_inf_conj_eq_bot {D : Data G} {p : ℕ} {B : Subgroup G} (hp : p.Prime)
    (hBM : B ≤ D.M) (hBcard : Nat.card B = p)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) :
    ∀ g : G, g ∉ D.M → B ⊓ conjSubgroup D.M g = ⊥ := by
  intro g hg
  refine eq_bot_iff.mpr ?_
  intro x hx
  obtain ⟨hxB, hxg⟩ := Subgroup.mem_inf.1 hx
  by_contra hx1
  have hxne : (⟨x, hxB⟩ : ↥B) ≠ 1 := by
    simpa using hx1
  have hdvd : orderOf (⟨x, hxB⟩ : ↥B) ∣ p := by
    have h1 : orderOf (⟨x, hxB⟩ : ↥B) ∣ Nat.card ↥B := orderOf_dvd_natCard _
    rwa [hBcard] at h1
  have hordB : orderOf (⟨x, hxB⟩ : ↥B) = p := by
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.1 h1) hxne
    · exact hp'
  have hxord : orderOf x = p := (Subgroup.orderOf_coe (⟨x, hxB⟩ : ↥B)).trans hordB
  have hzle : Subgroup.zpowers x ≤ D.M ⊓ conjSubgroup D.M g := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨D.M.zpow_mem (hBM hxB) k, (conjSubgroup D.M g).zpow_mem hxg k⟩
  have hcardz : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hxord]
  have hdvdK := Subgroup.card_subgroup_dvd_card
    (α := ↥(D.M ⊓ conjSubgroup D.M g))
    ((Subgroup.zpowers x).subgroupOf (D.M ⊓ conjSubgroup D.M g))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv, hcardz] at hdvdK
  exact hsp.2.2 g⁻¹ (fun h => hg (by simpa using D.M.inv_mem h)) hdvdK

section Certified

theorem s17_45_mBar_le_three (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G)
    (h1214 : F12.R1214 D) (h869 : F08.R869 D) (hW4a : Inputs1719.W4Lem14_6aSmall)
    {V₀ V L X : Subgroup G} {p n l r : ℕ} {C Dc : Subgroup G} {Gamma : Set G} {x : G}
    {A₀ A B : Subgroup G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) (hV₀ : V₀ ≠ ⊥)
    (hxM : x ∈ D.M) (hXsup : X = L ⊔ conjSubgroup L x) (hXne : X ≠ L)
    (hc : F08.Case8100ThreeR D ![L, conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, conjSubgroup L x] p X)
    (hAsyl : CFSG.ABGLocalTools.IsSylowOf r A X) (hBM : B ≤ D.M) (hBcard : Nat.card B = p)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hInF : InFSq 1 (A ⊔ B ⊔ D.T)) (hU : UniqueMax D.M (A ⊔ B ⊔ D.T)) :
    mBar D.M V₀ V ctx.hyp125.isElemAbelian ≤ 3 := by
  classical
  have h := ctx.hyp125
  have hpf := h.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hL := ctx.mem_calC
  have hLM : L ≤ D.M := hL.1.le
  have hXM : X ≤ D.M := by rw [ctx.X_eq]; exact TwelveTwentyThree.conjClosure_le hLM
  have hAM : A ≤ D.M := hAsyl.le.trans hXM
  have hp : p.Prime := (D.sig_prime p ctx.p_mem).1
  have hp2 : p ≠ 2 := (D.sig_prime p ctx.p_mem).2
  have hXsup' : UC22.conjClosure D.M L = L ⊔ conjSubgroup L x := ctx.X_eq ▸ hXsup
  have hXne' : UC22.conjClosure D.M L ≠ L := ctx.X_eq ▸ hXne
  have hswap := S18.p42_swap_data (D := D) hL hxM hXsup' hXne'
  have hMN : ¬ D.M ≤ normalizer (L : Set G) := fun h' => hswap.1 (D.sylowM.le.trans h')
  have h117 : C117 D V₀ V := ElevenNine.c117_of_hyp11 D h869 (h.hyp11 h127)
  have hLb : barSub V₀ V h.isElemAbelian L ≠ ⊥ := barSub_ne_bot_of_not_normal h h117 hL hMN
  by_contra hgt
  rw [not_le] at hgt
  have hk2 : D.k ≤ 2 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    split_ifs <;> norm_num
  have hBodd : Odd (Nat.card B) := by rw [hBcard]; exact hp.odd_of_ne_two hp2
  have hBres : B ≤ twoResidual (A ⊔ B ⊔ D.T) :=
    CFSG.GroupTheory.le_twoResidual_of_odd_card (le_sup_right.trans le_sup_left) hBodd
  have hBinf := s17_45_B_inf_conj_eq_bot hp hBM hBcard hsp
  have hB1 : B ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hBcard
    exact hp.one_lt.ne hBcard
  have hABTM : A ⊔ B ⊔ D.T ≤ D.M := sup_le (sup_le hAM hBM) D.sylowM.le
  have h1223 := twelve_twentyThree_three_two D hx h61 h66 h127 h1114 h162 hTor h1482 h183 h
    hV₀ hL.1 hL.2.2 hLb (Δ := {A ⊔ B ⊔ D.T})
    (by
      intro H hH
      rw [Finset.mem_singleton] at hH
      subst hH
      exact ⟨le_sup_right, hABTM⟩)
    (by rw [Finset.iSup_singleton]; exact hU) (fun _ => 1)
    (by
      intro H hH
      rw [Finset.mem_singleton] at hH
      subst hH
      exact hInF)
    (by
      intro H hH g hg hle
      rw [Finset.mem_singleton] at hH
      subst hH
      have hBg : B ≤ B ⊓ conjSubgroup D.M g := le_inf le_rfl (hBres.trans hle)
      rw [hBinf g hg] at hBg
      exact hB1 (le_bot_iff.1 hBg))
    (by rw [Finset.sup_singleton]) (by omega)
  have hKgroup : CFSG.Open.IsKGroup ↥(Mbar D.M V₀ V h.isElemAbelian) :=
    isKGroup_mbar D h.isElemAbelian hMs
  have hK : CFSG.IsKGroup ↥(Mbar D.M V₀ V h.isElemAbelian) :=
    CFSG.Assembly.kGroupAllSimple_of_kGroupNonab_of_catalogImp
      (fun X _ _ _ _ h => h) CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple hKgroup
  have hO2 : O2Trivial (Mbar D.M V₀ V h.isElemAbelian) :=
    fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D h hP hN h2
  have hcomp : IsComponentOf (barSub V₀ V h.isElemAbelian L)
      (Mbar D.M V₀ V h.isElemAbelian) :=
    barSub_mem_compBar_of_ne_bot h hL hLb
  have hYne : Mbar D.M V₀ V h.isElemAbelian ≠ ⊥ := by
    intro hbot
    exact hLb (le_bot_iff.1 (hbot ▸ hcomp.1))
  have hbasic : IsBasicModule (Mbar D.M V₀ V h.isElemAbelian) :=
    TwelveSeventeen.isBasicModule D hx h61 h127 h1214 h hYne
  have hXg : barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M L) =
      ⨆ g ∈ Mbar D.M V₀ V h.isElemAbelian,
        (barSub V₀ V h.isElemAbelian L).map (MulAut.conj g).toMonoidHom := by
    rw [barSub_conjClosure_eq_iSup_of_hyp125 h hLM, iSup_subtype']
  have hncard : (conjSet (barSub V₀ V h.isElemAbelian L)
      (Mbar D.M V₀ V h.isElemAbelian)).ncard ≤ 2 :=
    (S18.ncard_conjSet_barSub_le h hLM).trans (le_of_eq (ncard_eq_two_of_p42 hL hxM hXsup' hXne'))
  have hfix : fixV (barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ :=
    s15_Kbar_fixV_eq_bot_of_ne_bot h hV₀
      (barSub_mono V₀ V h.isElemAbelian (TwelveTwentyThree.conjClosure_le hLM))
      (barSub_subgroupOf_mbar_normal h.isElemAbelian (TwelveTwentyThree.conjClosure_le hLM)
        (TwelveTwentyThree.le_normalizer_conjClosure D.M L))
      (TwelveTwentyThree.barSub_conjClosure_ne_bot h.isElemAbelian hLb)
  have hm' : 3 < E3.mParam (Mbar D.M V₀ V h.isElemAbelian) := by simpa [mBar] using hgt
  have hle : E3.mParam (Mbar D.M V₀ V h.isElemAbelian) ≤
      bParam (barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M L))
        (Mbar D.M V₀ V h.isElemAbelian) + 2 := by
    have h2 : mBar D.M V₀ V h.isElemAbelian ≤
        bBar (UC22.conjClosure D.M L) D.M V₀ V h.isElemAbelian + 2 := by omega
    simpa [mBar, bBar] using h2
  have hW := hW4a (Vtil V₀ V h.isElemAbelian) (s15_Infra_vtil_sq_eq_one V₀ V h.isElemAbelian)
    (Mbar D.M V₀ V h.isElemAbelian) (barSub V₀ V h.isElemAbelian L)
    (barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M L))
  rcases hc with h3 | h4
  ·
    have hL2 : UC22.IsL2 (Bar2 L) 3 := h3.2.1
    have hs : IsSimpleGroup (Bar2 L) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
    obtain ⟨e⟩ := barSubBar2Equiv_of_isSimpleGroup h hL hLb hs
    have hL2b : UC22.IsL2 ↥(barSub V₀ V h.isElemAbelian L) 3 :=
      CFSG.Blueprint.LieModel.of_mulEquiv e hL2
    exact (hW hK hO2 hbasic hcomp hXg (Or.inl hL2b) hncard hfix hm' hle).elim
  ·
    have hSz : UC22.IsSz (Bar2 L) 5 := h4.2.1
    have hs : IsSimpleGroup (Bar2 L) :=
      (CFSG.LieType.Simplicity.fam_2b2_simplicity (Bar2 L) 2 5
        (CFSG.Blueprint.LieModel.suzukiModel hSz).2).2
    obtain ⟨e⟩ := barSubBar2Equiv_of_isSimpleGroup h hL hLb hs
    have hSzb : UC22.IsSz ↥(barSub V₀ V h.isElemAbelian L) 5 :=
      CFSG.Blueprint.LieModel.of_mulEquiv e hSz
    exact (hW hK hO2 hbasic hcomp hXg (Or.inr hSzb) hncard hfix hm' hle).elim

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
