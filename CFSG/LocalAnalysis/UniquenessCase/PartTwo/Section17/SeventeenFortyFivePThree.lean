module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SuzukiNotClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubConjClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubNotNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiagR42
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixHyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Mbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section CertifiedG2b


theorem s17_45_p_eq_three_of_bot (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h126 : R126 D) (h111 : W3Thm111 G) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h869 : F08.R869 D) (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (hW4a : Inputs1719.W4Lem14_6aSmall)
    {V L X : Subgroup G} {p n l r : ℕ} {C Dc : Subgroup G} {Gamma : Set G} {x : G}
    {A₀ : Subgroup G}
    (h1669 : Nat.card (⊥ : Subgroup G) ≤ 4 → MBarGT D.M ⊥ V 3)
    (ctx : Ctx17_42 D ⊥ V L X p n l C Dc Gamma)
    (hxM : x ∈ D.M) (hXsup : X = L ⊔ conjSubgroup L x) (hXne : X ≠ L)
    (h8100 : F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X)
    (hc : F08.Case8100ThreeR D ![L, conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, conjSubgroup L x] p X) : p = 3 := by
  classical
  rcases hc with h3 | h4
  · exact h3.2.2.1
  exfalso
  have h := ctx.hyp125
  have hpf := h.pairFacts
  have hMs : D.M ≤ stabTil ⊥ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hL := ctx.mem_calC
  have hLM : L ≤ D.M := hL.1.le
  have hXsup' : UC22.conjClosure D.M L = L ⊔ conjSubgroup L x := ctx.X_eq ▸ hXsup
  have hXne' : UC22.conjClosure D.M L ≠ L := ctx.X_eq ▸ hXne
  have hswap := S18.p42_swap_data (D := D) hL hxM hXsup' hXne'
  have hMN : ¬ D.M ≤ normalizer (L : Set G) := fun h' => hswap.1 (D.sylowM.le.trans h')
  have h117 : C117 D ⊥ V := ElevenNine.c117_of_hyp11 D h869 (h.hyp11 h127)
  have hLb : barSub ⊥ V h.isElemAbelian L ≠ ⊥ := barSub_ne_bot_of_not_normal h h117 hL hMN
  have hm3 : MBarGT D.M ⊥ V 3 := h1669 (by rw [Subgroup.card_bot]; norm_num)
  have hgt : 3 < mBar D.M ⊥ V h.isElemAbelian := (h.mBarGT_iff_lt_mBar 3).1 hm3
  have hk2 : D.k ≤ 2 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    split_ifs <;> norm_num
  have hUX : UniqueMax D.M X := uniqueMax_conjClosure_of_case34 D h61 h8100 (Or.inr h4)
  have hUX' : UniqueMax D.M (UC22.conjClosure D.M L) := ctx.X_eq ▸ hUX
  have h1223 := twelve_twentyThree_one D hx h61 h126 h111 h rfl hL.1 hL.2.2 hLb hUX'
  have hcomp2 : F12.IsComponentModO2 D.M (L ⊔ pCoreOf 2 D.M) :=
    isComponentModO2_sup_pCoreOf_of_mem_calC hL
  obtain ⟨t, htT, ht⟩ := hswap.2
  have hXLT : UC22.conjClosure D.M L ≤ (L ⊔ pCoreOf 2 D.M) ⊔ D.T := by
    rw [hXsup']
    refine sup_le (le_sup_left.trans le_sup_left) ?_
    rw [← ht]
    rintro y ⟨l, hl, rfl⟩
    have htT' : t ∈ (L ⊔ pCoreOf 2 D.M) ⊔ D.T := Subgroup.mem_sup_right htT
    have hl' : l ∈ (L ⊔ pCoreOf 2 D.M) ⊔ D.T :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_left hl)
    simpa [MulAut.conj_apply] using
      ((L ⊔ pCoreOf 2 D.M) ⊔ D.T).mul_mem (((L ⊔ pCoreOf 2 D.M) ⊔ D.T).mul_mem htT' hl')
        (((L ⊔ pCoreOf 2 D.M) ⊔ D.T).inv_mem htT')
  have hU : UniqueMax D.M ((L ⊔ pCoreOf 2 D.M) ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D hXLT
      (sup_le (sup_le hLM (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)) D.sylowM.le) hUX'
  have hbar : barSub ⊥ V h.isElemAbelian (UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M)) =
      barSub ⊥ V h.isElemAbelian (UC22.conjClosure D.M L) :=
    S18.barSub_conjClosure_sup_pCoreOf h hLM
  have hH : barSub ⊥ V h.isElemAbelian (UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M)) ≠ ⊥ := by
    rw [hbar]
    exact TwelveTwentyThree.barSub_conjClosure_ne_bot h.isElemAbelian hLb
  have hSz : UC22.IsSz (Bar2 L) 5 := h4.2.1
  have hfix : fixV (barSub ⊥ V h.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ := by
    rcases twelve_twentySix D h640 hFF h hcomp2 hU hH with hf | ⟨-, hcl, -⟩
    · rwa [hbar] at hf
    · obtain ⟨e⟩ := bar2_sup_pCoreOf_mulEquiv_of_mem_calC hL
      exact absurd hcl (not_classicalEvenAltG2Der_of_isSz
        (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hSz))
  have hKgroup : CFSG.Open.IsKGroup ↥(Mbar D.M ⊥ V h.isElemAbelian) :=
    isKGroup_mbar D h.isElemAbelian hMs
  have hK : CFSG.IsKGroup ↥(Mbar D.M ⊥ V h.isElemAbelian) :=
    CFSG.Assembly.kGroupAllSimple_of_kGroupNonab_of_catalogImp
      (fun X _ _ _ _ h => h) CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple hKgroup
  have hO2 : O2Trivial (Mbar D.M ⊥ V h.isElemAbelian) :=
    fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D h hP hN h2
  have hcomp : IsComponentOf (barSub ⊥ V h.isElemAbelian L) (Mbar D.M ⊥ V h.isElemAbelian) :=
    barSub_mem_compBar_of_ne_bot h hL hLb
  have hYne : Mbar D.M ⊥ V h.isElemAbelian ≠ ⊥ := by
    intro hbot
    exact hLb (le_bot_iff.1 (hbot ▸ hcomp.1))
  have hbasic : IsBasicModule (Mbar D.M ⊥ V h.isElemAbelian) :=
    TwelveSeventeen.isBasicModule D hx h61 h127 h1214 h hYne
  have hXg : barSub ⊥ V h.isElemAbelian (UC22.conjClosure D.M L) =
      ⨆ g ∈ Mbar D.M ⊥ V h.isElemAbelian,
        (barSub ⊥ V h.isElemAbelian L).map (MulAut.conj g).toMonoidHom := by
    rw [barSub_conjClosure_eq_iSup_of_hyp125 h hLM, iSup_subtype']
  have hncard : (conjSet (barSub ⊥ V h.isElemAbelian L)
      (Mbar D.M ⊥ V h.isElemAbelian)).ncard ≤ 2 :=
    (S18.ncard_conjSet_barSub_le h hLM).trans
      (le_of_eq (ncard_eq_two_of_p42 hL hxM hXsup' hXne'))
  have hm' : 3 < E3.mParam (Mbar D.M ⊥ V h.isElemAbelian) := by simpa [mBar] using hgt
  have hle : E3.mParam (Mbar D.M ⊥ V h.isElemAbelian) ≤
      bParam (barSub ⊥ V h.isElemAbelian (UC22.conjClosure D.M L))
        (Mbar D.M ⊥ V h.isElemAbelian) + 2 := by
    have h2 : mBar D.M ⊥ V h.isElemAbelian ≤
        bBar (UC22.conjClosure D.M L) D.M ⊥ V h.isElemAbelian + 2 := by omega
    simpa [mBar, bBar] using h2
  have hs : IsSimpleGroup (Bar2 L) :=
    (CFSG.LieType.Simplicity.fam_2b2_simplicity (Bar2 L) 2 5
      (CFSG.Blueprint.LieModel.suzukiModel hSz).2).2
  obtain ⟨e⟩ := barSubBar2Equiv_of_isSimpleGroup h hL hLb hs
  have hSzb : UC22.IsSz ↥(barSub ⊥ V h.isElemAbelian L) 5 :=
    CFSG.Blueprint.LieModel.of_mulEquiv e hSz
  exact hW4a (Vtil ⊥ V h.isElemAbelian) (s15_Infra_vtil_sq_eq_one ⊥ V h.isElemAbelian)
    (Mbar D.M ⊥ V h.isElemAbelian) (barSub ⊥ V h.isElemAbelian L)
    (barSub ⊥ V h.isElemAbelian (UC22.conjClosure D.M L)) hK hO2 hbasic hcomp hXg
    (Or.inr hSzb) hncard hfix hm' hle

end CertifiedG2b

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
