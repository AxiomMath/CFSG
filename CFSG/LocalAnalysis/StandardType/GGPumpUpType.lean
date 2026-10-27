module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeO1ppModels
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158InnHolds2
import CFSG.LocalAnalysis.StandardType.GGPumpUpCentreless
import CFSG.LocalAnalysis.StandardType.GGPumpUpLabels
import CFSG.LocalAnalysis.StandardType.GGPumpUpSplitA
import CFSG.LocalAnalysis.StandardType.GGPumpUpOuter
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144IInn
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I161a2
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeO1pp
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Pass

public section

namespace CFSG.GGQ2Prime

open CFSG.Assembly CFSG.StandardType
open CFSG.Open
open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem pumpUpTypeInput_holds :
    PumpUpTypeInput := by
  intro K _ _ W Wk ζ ξ Q A h
  by_cases hInner : CFSG.LocalAnalysis.GLTheoremA.K144.I144Inner K ζ
  ·
    have hfix : autFix ζ = fixSubgroup ζ := by
      ext x
      simp only [mem_autFix, mem_fixSubgroup]
    have hW_le : W ≤ fixSubgroup ζ := hfix ▸ h.W_comp.1
    have hW_sub : CFSG.Open.IsSubnormal W (fixSubgroup ζ) := hfix ▸ h.W_comp.2.1
    have hW_q : CFSG.Open.IsQuasisimple W := h.W_comp.2.2
    have hSC : CFSG.Open.StatedClassicalModel W .PSU 5 2 1 :=
      CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by norm_num : (5 : ℕ) ≠ 0) h.W_model
    have hcardW : Nat.card W = 13685760 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hSC
    have h3W : 3 ∣ Nat.card W := by rw [hcardW]; norm_num
    have hJ : CFSG.Open.GLAPComponent 3 (fixSubgroup ζ) W :=
      CFSG.HardMathSupport.Solomon.Coordinator.i253_glaPComponent_of_subnormal
        hW_le hW_sub hW_q h3W
    obtain ⟨e0⟩ := CFSG.LocalAnalysis.GLTheoremA.I141F.centerQuot_equiv_pSimple
      (p := 3) (by norm_num) hJ hW_q
    have hcenter : Subgroup.center W = ⊥ := pumpUp_u52_center h
    let eW : W ≃* W ⧸ Subgroup.center W :=
      ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
    let e : W ≃* PSimple 3 W := eW.trans e0
    have hcatW : catalogIs W CFSG.LocalAnalysis.GLTheoremA.S9.isU5two :=
      catalogIs_u52_of_model h.W_model
    have hcatPS : catalogIs (PSimple 3 W) CFSG.LocalAnalysis.GLTheoremA.S9.isU5two :=
      (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr e).1 hcatW
    have hcat : catalogIs (PSimple 3 W) CFSG.LocalAnalysis.GLTheoremA.K144.I144Cat := by
      rcases hcatPS with ⟨i, hi, hf⟩
      exact ⟨i, Or.inr (Or.inl hi), hf⟩
    have hmark : CFSG.Open.GLAMarking K (fun lab _ _ _ _ _ => lab.n = 1) :=
      CFSG.LocalAnalysis.GLTheoremA.K144I.i144InnFact_holds
        K ζ W h.quasi h.ζ_cube hJ hcat hInner
    obtain ⟨-, lab, hlab, hraw⟩ := CFSG.StandardType.Canonical.largeEvenMarking_markedModel hmark
    obtain ⟨R, _instR, I, F, -, -, θ, hP, hm⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    have hmS : MarkedModel lab (K ⧸ Subgroup.center K) :=
      MarkedModel.of_mulEquiv θ.symm hm
    have h11S : 11 ∣ Nat.card (K ⧸ Subgroup.center K) := pumpUp_eleven_dvd h
    have hcard : Nat.card (K ⧸ Subgroup.center K) = SporadicShape.labOrd lab :=
      (SporadicShape.labOrd_eq_of_rawDatum hlab
        (CFSG.StandardType.Canonical.largeEvenRawDatum_imp hlab (fun R _ I F hq => hq.2.1)
          (fun R _ I F hq _ => by
            obtain ⟨-, -, θ', -⟩ := hq
            exact (Nat.card_congr θ'.toEquiv).symm)
          hraw)).symm
    have h11lab : 11 ∣ SporadicShape.labOrd lab := by
      rw [← hcard]; exact h11S
    obtain ⟨tag, rank, n⟩ := lab
    have hn : n = 1 := hP
    have hcases := label_one_eleven_cases ⟨tag, rank, n⟩ hlab hn h11lab
    rcases hcases with hA | ⟨htwA, hrank⟩ | ⟨hBCDD, hrank⟩ | hE6 | htwE6 | hE7 | hE8
    ·
      subst hA
      simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmS
      subst hn
      have hS : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSL (rank + 1) 2 1 :=
        CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hmS
      simp only [LargeEvenInLambda2] at hlab
      have hrank2 : 2 ≤ rank := by
        have hne1 : rank ≠ 1 := by
          intro hr1
          have h2 := hlab.2.2 hr1
          omega
        have hge1 : 1 ≤ rank := hlab.2.1
        omega
      have hm3 : 3 ≤ rank + 1 := by omega
      exact (pumpUp_not_psl_two h (rank + 1) hm3 hS).elim
    ·
      subst htwA
      have hrank : 4 ≤ rank := hrank
      simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmS
      subst hn
      have hS : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSU (rank + 1) 2 1 :=
        CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hmS
      by_cases hr4 : rank = 4
      · subst hr4
        exact (pumpUp_not_u52 h hS).elim
      · have hr5 : 5 ≤ rank := by omega
        exact Or.inl ⟨rank + 1, by omega, hS⟩
    ·
      have hrank : 5 ≤ rank := hrank
      rcases hBCDD with hB | hC | hD | htwD
      · subst hB
        simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmS
        subst hn
        have hS : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSp rank 2 1 :=
          CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hmS
        exact Or.inr (Or.inl ⟨rank, hrank, Or.inl hS⟩)
      · subst hC
        simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmS
        subst hn
        have hS : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSp rank 2 1 :=
          CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hmS
        exact Or.inr (Or.inl ⟨rank, hrank, Or.inl hS⟩)
      · subst hD
        have hr3 : rank ≠ 3 := by omega
        simp only [MarkedModel, markTag, markRank, markChar, markDeg, if_neg hr3] at hmS
        subst hn
        have hS : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .POmegaPlus rank 2 1 :=
          CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hmS
        exact Or.inr (Or.inl ⟨rank, hrank, Or.inr (Or.inl hS)⟩)
      · subst htwD
        have hr2 : rank ≠ 2 := by omega
        have hr3 : rank ≠ 3 := by omega
        simp only [MarkedModel, markTag, markRank, markChar, markDeg, if_neg hr2, if_neg hr3] at hmS
        subst hn
        have hS : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .POmegaMinus rank 2 1 :=
          CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hmS
        exact Or.inr (Or.inl ⟨rank, hrank, Or.inr (Or.inr hS)⟩)
    ·
      subst hE6
      simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmS
      subst hn
      have hS : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .E6 0 2 1 :=
        CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hmS
      exact Or.inr (Or.inr (Or.inl hS))
    ·
      subst htwE6
      simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmS
      subst hn
      have hS : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 1 :=
        CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hmS
      exact Or.inr (Or.inr (Or.inr (Or.inl hS)))
    ·
      subst hE7
      simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmS
      subst hn
      have hS : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .E7 0 2 1 :=
        CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hmS
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hS))))
    ·
      subst hE8
      simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hmS
      subst hn
      have hS : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .E8 0 2 1 :=
        CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hmS
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hS))))
  ·
    exact (pumpUp_not_outer h hInner).elim

end CFSG.GGQ2Prime

end
