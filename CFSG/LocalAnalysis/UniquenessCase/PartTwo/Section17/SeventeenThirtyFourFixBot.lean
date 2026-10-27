module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFiveProof
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Exc
public import CFSG.GroupTheory.IrreducibleAbelianAction
public import CFSG.Quasithin.Background.RonanF615QTK
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HeJ2Local17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barSub_jOf_commute_of_isSU3
    {D : Data G} {V : Subgroup G} (h : Hyp125 D ⊥ V) {L : Subgroup G} {n : ℕ}
    (hL : L ∈ calC D.M) (hLb : barSub ⊥ V h.isElemAbelian L ≠ ⊥)
    (hshape : IsSU3 (Bar2 L) n) :
    ⁅barSub ⊥ V h.isElemAbelian (F12.jOf D.T), barSub ⊥ V h.isElemAbelian L⁆ = ⊥ := by
  by_contra hJ'
  have hV := h.isElemAbelian
  set Lbar : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV L with hLbardef
  have hLM : L ≤ D.M := hL.1.le
  have hmove : ∃ A : Subgroup (MulAut (Vtil ⊥ V hV)),
      IsFFStarOffender (Mbar D.M ⊥ V hV) A ∧ ⁅A, Lbar⁆ ≠ ⊥ := by
    by_contra hno
    push Not at hno
    have hle : ffJ (Mbar D.M ⊥ V hV) ≤ Subgroup.centralizer (Lbar : Set _) := by
      refine iSup₂_le fun A hA => ?_
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 (hno A hA)
    have hJle : barSub ⊥ V hV (F12.jOf D.T) ≤ Subgroup.centralizer (Lbar : Set _) :=
      (S18.barSub_jOf_le_ffJ h).trans hle
    exact hJ' ((Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := barSub ⊥ V hV (F12.jOf D.T)) (H₂ := Lbar)).2 hJle)
  obtain ⟨A, hAoff, hAL⟩ := hmove
  have hA_le : A ≤ Mbar D.M ⊥ V hV := hAoff.1
  letI : Module (ZMod 2) (Additive (Vtil ⊥ V hV)) :=
    CFSG.GroupTheory.elemModule 2 (s15_Infra_vtil_sq_eq_one ⊥ V hV)
  let ρ : Representation (ZMod 2) ↥(Mbar D.M ⊥ V hV) (Additive (Vtil ⊥ V hV)) :=
    (CFSG.RankThree.FFModules.autRep (Vtil ⊥ V hV)).comp
      (Mbar D.M ⊥ V hV).subtype
  have hρinj : Function.Injective ρ :=
    CFSG.RankThree.FFModules.autRep_injective.comp
      (Subgroup.subtype_injective (Mbar D.M ⊥ V hV))
  let L' : Subgroup ↥(Mbar D.M ⊥ V hV) := Lbar.subgroupOf (Mbar D.M ⊥ V hV)
  let A' : Subgroup ↥(Mbar D.M ⊥ V hV) := A.subgroupOf (Mbar D.M ⊥ V hV)
  have hAL' : ⁅L', A'⁆ ≠ ⊥ := by
    intro hbot
    apply hAL
    rw [Subgroup.commutator_comm]
    have hmap := CFSG.commutator_subgroupOf_map_eq (Mbar D.M ⊥ V hV) A Lbar hA_le
      (barSub_mono ⊥ V hV hLM)
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hrep : CFSG.RankThree.FFModules.repMulAut
      (CFSG.RankThree.FFModules.autRep (Vtil ⊥ V hV)) =
      MonoidHom.id (MulAut (Multiplicative (Additive (Vtil ⊥ V hV)))) := by
    ext φ w
    rfl
  have hmapA : A'.map (CFSG.RankThree.FFModules.repMulAut ρ) = A := by
    have hcomp : CFSG.RankThree.FFModules.repMulAut ρ = (Mbar D.M ⊥ V hV).subtype := by
      rw [show CFSG.RankThree.FFModules.repMulAut ρ =
          (CFSG.RankThree.FFModules.repMulAut
            (CFSG.RankThree.FFModules.autRep (Vtil ⊥ V hV))).comp
            (Mbar D.M ⊥ V hV).subtype from rfl, hrep]
      exact MonoidHom.id_comp _
    rw [hcomp]
    exact Subgroup.map_subgroupOf_eq_of_le hA_le
  have hAcal : A' ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.Ext.calP ρ := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.K148.mem_calP_iff]
    have hiff := CFSG.RankThree.FFModules.isFFStarOffender_map_iff hρinj
      (A := A') (Y := Mbar D.M ⊥ V hV) (by rw [hmapA]; exact hA_le)
    rw [hmapA] at hiff
    exact hiff.1 hAoff
  have hcomp : CFSG.Open.IsComponentOf L' ⊤ := by
    have hc := barSub_mem_compBar_of_ne_bot h hL hLb
    exact CFSG.Quasithin.RonanF615.isComponentOf_subgroupOf hc
  have hSU : IsSU3 ↥Lbar n := isSU3_barSub h hL hLb hshape
  have hSU' : IsSU3 ↥L' n :=
    uc22p20p_isSU3_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (barSub_mono ⊥ V hV hLM)).symm hSU
  exact hAL' (CFSG.LocalAnalysis.UniquenessCase.UC22.K148.su3_commute_calP hρinj hcomp hSU' hAcal)

theorem fixV_conjClosure_eq_bot_of_ctx17_33
    (D : Data G) {V₀ V : Subgroup G} (h869 : F08.R869 D) (h127 : R127 D)
    (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg) (hSyl : UCK.U3Syl)
    {L : Subgroup G} {n : ℕ} (c : Ctx17_33 D V₀ V L n) :
    fixV (barSub V₀ V c.hyp125.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ := by
  have hV := c.hyp125
  have hL := c.mem_calC
  have hnt : ¬ F08.Thin8 L := not_thin_of_isSU3 hSyl c.shape
  have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ := by
    rcases eq_or_ne V₀ ⊥ with hV0 | hV0
    · subst hV0
      exact barSub_ne_bot_of_not_thin_bot h869 h127 hV hL hnt
    · exact barSub_ne_bot_of_not_thin hV
        (ElevenNine.c117_of_hyp11 D h869 (Hyp125.hyp11 h127 hV)) hL hnt
  have hcomp : F12.IsComponentModO2 D.M (L ⊔ pCoreOf 2 D.M) :=
    isComponentModO2_sup_pCoreOf_of_mem_calC hL
  have hUK : UniqueMax D.M ((L ⊔ pCoreOf 2 D.M) ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D
      (sup_le ((le_sup_left : L ≤ L ⊔ pCoreOf 2 D.M).trans le_sup_left) le_sup_right)
      (sup_le (sup_le hL.1.le (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)) D.sylowM.le)
      (Inputs1719.uniqueMax_sup_T_of_not_thin h869 hL hnt)
  have hbar : barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M)) =
      barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) :=
    S18.barSub_conjClosure_sup_pCoreOf hV hL.1.le
  have hH : barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M)) ≠ ⊥ := by
    rw [hbar]
    exact TwelveTwentyThree.barSub_conjClosure_ne_bot hV.isElemAbelian hL1
  rcases twelve_twentySix D h640 hFF hV hcomp hUK hH with hfix | ⟨hV0, -, hJ⟩
  · rwa [hbar] at hfix
  · exfalso
    subst hV0
    have hJ' : ⁅barSub ⊥ V hV.isElemAbelian (F12.jOf D.T),
        barSub ⊥ V hV.isElemAbelian L⁆ ≠ ⊥ := by
      rwa [barSub_sup_pCoreOf_eq_of_hyp125 hV hL.1.le] at hJ
    exact hJ' (barSub_jOf_commute_of_isSU3 hV hL hL1 c.shape)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
