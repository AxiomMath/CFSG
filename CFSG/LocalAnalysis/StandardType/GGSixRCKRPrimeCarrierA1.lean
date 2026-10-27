module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnSpecs
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierA1Cover
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierA1Action
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCtx
import CFSG.LocalAnalysis.StandardType.GGRootDetectCore
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapLiftSplit
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine
import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

theorem rckCarrierA1_holds :
    RCKCarrierA1 := by
  intro τ p₀ S a hT p hp hp2 hap i h hq h1 hqs
  classical
  obtain ⟨β, hβ, hΨ⟩ := rckA1_componentRoots_eq_pair i h1
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  have hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
    have hs' := hs
    rw [hΨ] at hs' ⊢
    exact rckA1_twistInner_pair hβ hs' (rho_iterate_neg S s β)
  obtain ⟨σ, z, hσ, hzZ, hnorm, hz⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_untwistT_Z S hT i hs0 hinner
  obtain ⟨hhs, φ₀, hφr₀, hφk₀⟩ := rckA1_exists_cover S hT i hΨ hs hmin σ hσ hnorm hz hq hqs
  obtain ⟨φ, hφr, hφk⟩ : ∃ φ : (ggU .PSL 2 (h * s)).K →* ModGL τ GGL,
      φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        φ.ker ≤ Subgroup.center (ggU .PSL 2 (h * s)).K := ⟨φ₀, hφr₀, hφk₀⟩
  have h4 : 4 ≤ 2 ^ (h * s) :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (h * s) := Nat.pow_le_pow_right (by norm_num) hhs
  have hQ : 4 ≤ S.D.q ^ s := by rw [hq, ← pow_mul]; exact h4
  have hperf := isPerfect_CQ_of_four_le_pow S i σ hσ hQ
  refine ⟨ggU .PSL 2 (h * s), φ, rfl, ?_, hφr, hφk, ?_, ?_, ?_, ?_, ?_⟩
  · refine Or.inl ⟨.PSL, 2, Or.inl rfl,
      ⟨Nat.prime_two, le_trans (by norm_num) hhs, le_rfl, ?_, ?_⟩, rfl⟩
    · intro he
      have : 2 ^ (h * s) = 2 := (Prod.mk.inj he).2
      omega
    · intro he
      have : 2 ^ (h * s) = 3 := (Prod.mk.inj he).2
      omega
  · show Finite (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)))
    infer_instance
  · show Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)))
    have hcard : Nat.card (GaloisField 2 (h * s)) = 2 ^ (h * s) :=
      GaloisField.card 2 (h * s) (by omega)
    have := Fintype.ofFinite (GaloisField 2 (h * s))
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
      (show 4 ≤ (Finset.univ : Finset (GaloisField 2 (h * s))).card by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]; exact h4)
    exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨t, ht⟩
  · exact CFSG.SeitzReduction.LinearPilot.oddCentralSplit_specialLinearGroup (m := 1)
      (F := GaloisField 2 (h * s))
  · exact CFSG.StandardType.RCKK1I.rckExists_longRoot _ (by show 0 < 1; norm_num)
  · intro b hb
    obtain ⟨r, hr, hrx⟩ := rckA1_torus_conj_inner S hT i hΨ hs hmin σ hzZ hnorm hz hperf hb
    rw [← hφr] at hr
    obtain ⟨u, rfl⟩ := hr
    refine CFSG.StandardType.RootDetect.ggPsiInnerDiag_of_centralizes _ (a := u⁻¹) fun y => ?_
    have key := hrx (φ (u⁻¹ * y * u)) (by rw [← hφr]; exact ⟨_, rfl⟩)
    simp only [map_mul, map_inv] at key ⊢
    calc (b * (φ u)⁻¹)⁻¹ * φ y * (b * (φ u)⁻¹)
        = φ u * (b⁻¹ * (φ u * ((φ u)⁻¹ * φ y * φ u) * (φ u)⁻¹) * b) * (φ u)⁻¹ := by group
      _ = φ y := by rw [← key]; group

end CFSG.StandardType.RCKRP
