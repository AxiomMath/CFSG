module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeO1ppModels
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Transfer
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVU58
import CFSG.LocalAnalysis.StandardType.GGPumpUpQuotComp
import CFSG.LocalAnalysis.StandardType.GGPumpUpCentreless
import CFSG.LocalAnalysis.StandardType.GGPumpUpU58
import CFSG.LocalAnalysis.StandardType.GGPumpUpFieldLeaf
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144OutHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144IOut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeO1pp
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVQuasi
public import CFSG.Walter.J1Props
public import Certificates.Certificate8166
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144FieldConj
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144IInn
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144OutFalse

public section

namespace CFSG.GGQ2Prime

open CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem pptp7_eq_twA_of_canon {lab : CFSG.Assembly.LargeEvenLabel}
    (h1 : (CFSG.LocalAnalysis.GLTheoremA.canonLabel lab).n = 3)
    (h2 : (CFSG.LocalAnalysis.GLTheoremA.canonLabel lab).tag = .twA)
    (h3 : (CFSG.LocalAnalysis.GLTheoremA.canonLabel lab).rank = 4) : lab = ⟨.twA, 4, 3⟩ := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;>
    simp only [CFSG.LocalAnalysis.GLTheoremA.canonLabel] at h1 h2 h3 ⊢ <;>
    (try split_ifs at h1 h2 h3) <;> simp_all

theorem pumpUp_not_outer
    {K : Type} [Group K] [Finite K] {W Wk : Subgroup K} {ζ ξ : MulAut K}
    {Q A : Subgroup (MulAut K)}
    (h : PumpUpAut W Wk ζ ξ Q A)
    (houter : ¬ CFSG.LocalAnalysis.GLTheoremA.K144.I144Inner K ζ) : False := by
  have hWq : CFSG.Open.IsQuasisimple W := h.W_comp.2.2
  have hWcard : Nat.card W = 13685760 := by
    have hB : CFSG.Blueprint.LieModel W .PSU 5 2 1 :=
      CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
        (t := .PSU) (by simp [CFSG.Blueprint.classicalTags]) h.W_model
    have hSC : CFSG.Open.StatedClassicalModel W .PSU 5 2 1 :=
      hB.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
    exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hSC
  have h3W : 3 ∣ Nat.card W := by rw [hWcard]; norm_num
  have haf : fixSubgroup ζ = CFSG.GGQ2Prime.autFix ζ := Subgroup.ext (fun _ => Iff.rfl)
  have hJ : CFSG.Open.GLAPComponent 3 (fixSubgroup ζ) W := by
    have hJ' : CFSG.Open.GLAPComponent 3 (CFSG.GGQ2Prime.autFix ζ) W :=
      CFSG.HardMathSupport.Solomon.Coordinator.i253_glaPComponent_of_subnormal
        h.W_comp.1 h.W_comp.2.1 hWq h3W
    rwa [← haf] at hJ'
  have hcenW : Subgroup.center W = ⊥ := pumpUp_u52_center h
  have hcatW : CFSG.Yardstones.Md0ec50421ce4.catalogIs W
      CFSG.LocalAnalysis.GLTheoremA.S9.isU5two := catalogIs_u52_of_model h.W_model
  obtain ⟨eWq⟩ := CFSG.LocalAnalysis.GLTheoremA.I141F.centerQuot_equiv_pSimple
    Nat.prime_three hJ hWq
  let eW : ↥W ≃* CFSG.Yardstones.Md0ec50421ce4.PSimple 3 W :=
    ((QuotientGroup.quotientMulEquivOfEq hcenW).trans QuotientGroup.quotientBot).symm.trans eWq
  have hcatPS : CFSG.Yardstones.Md0ec50421ce4.catalogIs
      (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 W)
      CFSG.LocalAnalysis.GLTheoremA.S9.isU5two :=
    (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eW).1 hcatW
  have hcat : CFSG.Yardstones.Md0ec50421ce4.catalogIs
      (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 W)
      CFSG.LocalAnalysis.GLTheoremA.K144.I144Cat := by
    obtain ⟨i, hi, he⟩ := hcatPS
    exact ⟨i, Or.inr (Or.inl hi), he⟩
  have hchevS : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 (K ⧸ Subgroup.center K) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo
      (CFSG.StandardType.isChevTwo_of_largeEvenMarking h.lie)
  have hmk := CFSG.LocalAnalysis.GLTheoremA.K144I.i144OutFact_holds
    K ζ W h.quasi hchevS h.ζ_cube hJ hcat houter
  obtain ⟨hcomm, lab, hlam, hraw⟩ := hmk
  have hnot : ¬ (lab.tag = .triD4 ∧ (3 : ℕ) = 3) := by
    obtain ⟨R, _, I, F, hsR, hnaR, θR, hPF⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    rintro ⟨ht, -⟩
    rcases hPF.1 with h1 | h1
    · exact h1 ht
    · exact absurd rfl h1
  have hlabK : HasLabel K (fun l => l = lab) :=
    ⟨hcomm, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨hβ3, hJb, hlabJ⟩ := pumpUp_quotient_component h
  have hlabS : HasLabel (K ⧸ Subgroup.center K) (fun l => l = lab) :=
    hasLabel_centerQuot hlabK
  have hcenS : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    center_centerQuot_eq_bot h.quasi
  have hnin : ¬ InnDiagKind (K ⧸ Subgroup.center K) lab
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.centerQuotAut K ζ) :=
    fun hin => houter (CFSG.LocalAnalysis.GLTheoremA.K144.inner_of_innDiagKind h.quasi hin)
  have key : FieldKind (K ⧸ Subgroup.center K) lab
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.centerQuotAut K ζ) → False := by
    intro hfld
    have hfp := CFSG.LocalAnalysis.GLTheoremA.Y10GField.fldPiece_reduced_holds
      (K ⧸ Subgroup.center K) 3 (CFSG.LocalAnalysis.GLTheoremA.Y10F.centerQuotAut K ζ)
      (W.map (QuotientGroup.mk' (Subgroup.center K))) lab ⟨.twA, 4, 1⟩
      Nat.prime_three (by norm_num) hcenS hfld hnot hβ3 hlabJ hJb
    obtain ⟨h1, h2, h3⟩ := hfp
    have h1' : (CFSG.LocalAnalysis.GLTheoremA.canonLabel lab).n = 3 := by
      simpa [CFSG.LocalAnalysis.GLTheoremA.canonLabel] using h1
    have h2' : (CFSG.LocalAnalysis.GLTheoremA.canonLabel lab).tag = .twA := by
      simpa [CFSG.LocalAnalysis.GLTheoremA.canonLabel] using h2
    have h3' : (CFSG.LocalAnalysis.GLTheoremA.canonLabel lab).rank = 4 := by
      simpa [CFSG.LocalAnalysis.GLTheoremA.canonLabel] using h3
    have hlab_eq : lab = ⟨.twA, 4, 3⟩ := pptp7_eq_twA_of_canon h1' h2' h3'
    subst hlab_eq
    obtain ⟨hcomm', lab', hlam', hraw'⟩ :=
      CFSG.StandardType.Canonical.largeEvenMarking_markedModel hfld
    obtain ⟨R, _, I, F, hsR, hnaR, θR, hP, hM⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw'
    have hM' : CFSG.Blueprint.LieModel R .PSU 5 2 3 := by
      rw [hP.1] at hM
      simpa only [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
        CFSG.StandardType.markRank, CFSG.StandardType.markChar,
        CFSG.StandardType.markDeg] using hM
    have hSC_R : CFSG.Open.StatedClassicalModel R .PSU 5 2 3 :=
      hM'.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
    have eSR : (K ⧸ Subgroup.center K) ≃* R :=
      ((QuotientGroup.quotientMulEquivOfEq hcenS).trans QuotientGroup.quotientBot).symm.trans θR
    have hSC_S : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 5 2 3 :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eSR.symm hSC_R
    exact CFSG.GGQ2Prime.PumpUpU58.u58_pumpUp_false h
      (CFSG.Models.lieModel_of_statedClassicalModel hSC_S)
  rcases CFSG.LocalAnalysis.GLTheoremA.Y10GField.cls_of_families
      CFSG.LocalAnalysis.GLTheoremA.Y10GField.ClsLin_holds
      CFSG.LocalAnalysis.GLTheoremA.Y10GField.ClsUni_holds
      CFSG.LocalAnalysis.GLTheoremA.Y10GField.ClsSymp_holds
      CFSG.LocalAnalysis.GLTheoremA.Y10GClsOrth.clsOrth_holds
      CFSG.LocalAnalysis.GLTheoremA.Y10GClsExc.clsExc_holds
      (K ⧸ Subgroup.center K) 3 (CFSG.LocalAnalysis.GLTheoremA.Y10F.centerQuotAut K ζ) lab
      Nat.prime_three (by norm_num) hcenS hlabS hβ3 with hin | hfld | hD
  · exact hnin hin
  · exact key hfld
  ·
    obtain ⟨hDtag, hDrk, -⟩ := hD
    by_cases hfld2 : FieldKind (K ⧸ Subgroup.center K) lab
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.centerQuotAut K ζ)
    · exact key hfld2
    · have hcatJb : CFSG.Yardstones.Md0ec50421ce4.catalogIs
          (CFSG.Yardstones.Md0ec50421ce4.PSimple 3
            (W.map (QuotientGroup.mk' (Subgroup.center K))))
          CFSG.LocalAnalysis.GLTheoremA.K144.I144Cat := by
        obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_map
          Nat.prime_three (QuotientGroup.mk' (Subgroup.center K)) hJ hJb
        exact (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eJ).1 hcat
      exact CFSG.LocalAnalysis.GLTheoremA.K144.out_D4_false
        CFSG.StandardType.ggLabelRigidInput_holds
        CFSG.LocalAnalysis.GLTheoremA.K144.triPiece_holds
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
        hcenS hlabS hDtag hDrk hβ3 hnin hfld2 hJb hcatJb

end CFSG.GGQ2Prime

end