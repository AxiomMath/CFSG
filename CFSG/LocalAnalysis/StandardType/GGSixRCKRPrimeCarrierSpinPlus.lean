module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnSpecs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSpinPlusCover
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSpinPlusModel
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierA1Action
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4FixMain
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCtx
import CFSG.LocalAnalysis.StandardType.GGRootDetectCore
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SuN
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfAssemble

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem rckCarrierSpinPlus_holds :
    RCKCarrierSpinPlus := by
  intro τ p₀ S a hT p hp hp2 hap i h hq hk h4 hn _
  classical
  have hτ := rckSpin_tag S hT i h4 hn
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have hinner := rckD_twistInner hk h4 hn
  obtain ⟨σ, z, -, hzZ, hnorm, hz⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_untwistT_Z S hT i hs0 hinner
  obtain ⟨φ, hφr, hφk⟩ := rckSpin_cover S hτ hT hp hp2 hap i h4 hn hinner hq
  have hhs : 0 < h * s := Nat.mul_pos (carrierSL_exp_pos S hq) hs0
  obtain ⟨hstd, hfin, hperf, hodd, hlong⟩ := rckSpin_ggU_facts h4 hhs
  have hdet := CFSG.LocalAnalysis.GLTheoremA.T171Sh.det_cartan_eq_four_of_typeD
    (isRootComponent_componentRoots i) h4 hn
  have h2 : 2 < (componentRoots (rootCharHom a) i).ncard := by
    rw [hn]
    have h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i) - 1 := by omega
    calc 2 < 2 * 4 * 3 := by norm_num
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left 2 h4) h3
  have hCperf := CFSG.LocalAnalysis.GLTheoremA.T171Sh.isPerfect_CQ_of_simplyLaced hτ i h2 σ
  refine ⟨ggU .POmegaPlus (compRank (componentRoots (rootCharHom a) i)) (h * s), φ, rfl, hstd,
    hφr, hφk, hfin, hperf, hodd, hlong, ?_⟩
  intro b hb
  obtain ⟨r, hr, hrx⟩ := rck_torus_conj_inner_of_commute S hT i hs hmin σ
    (fun _ hg hc => CFSG.LocalAnalysis.GLTheoremA.T171Sh.mem_CQ_of_commute_of_det_four i hdet σ
      hg hc) hzZ hnorm hz hCperf hb
  rw [← hφr] at hr
  obtain ⟨u, rfl⟩ := hr
  refine CFSG.StandardType.RootDetect.ggPsiInnerDiag_of_centralizes _ (a := u⁻¹) fun y => ?_
  have key := hrx (φ (u⁻¹ * y * u)) (by rw [← hφr]; exact ⟨_, rfl⟩)
  simp only [map_mul, map_inv] at key ⊢
  calc (b * (φ u)⁻¹)⁻¹ * φ y * (b * (φ u)⁻¹)
      = φ u * (b⁻¹ * (φ u * ((φ u)⁻¹ * φ y * φ u) * (φ u)⁻¹) * b) * (φ u)⁻¹ := by group
    _ = φ y := by rw [← key]; group

end CFSG.StandardType.RCKRP

end
