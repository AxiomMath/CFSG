module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestFieldBasic
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestOutdiag
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstar
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256q2
import CFSG.ClassicalInvolution.RouteD.G2D4T3Free
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeALocalBase
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Orb
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthAux.Descent
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownMGmat
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinTwoFam
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Entry
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviFields
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightChoice
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidSetup
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidTheta
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporAll
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCo
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFi23
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN3
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHe3
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporJ3
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporLy
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporSuz
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterTriality
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporFi24
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129h
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129i
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129j
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma138b
import CFSG.Quasithin.Background.G1Basic
import CFSG.StronglyEmbedded.UniqueCoset
import Certificates.Kernel.J4Count.Cent11Base
import Certificates.Kernel.J4Count.Fix11

public section

namespace CFSG.StandardType

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.Universal

theorem ggPsiInnerDiag_sl_of_cube_of_ringAut_sq
    {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ} (hm : 2 ≤ m)
    (hσsq : ∀ σ : F ≃+* F, σ * σ = 1)
    {X : Type*} [Group X] {ψ : SpecialLinearGroup (Fin (m + 1)) F →* X}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    {c : X} (hc : c ∈ Subgroup.normalizer (ψ.range : Set X)) (hc3 : c ^ 3 = 1) :
    GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ c := by
  have hn : 3 ≤ m + 1 := by omega
  obtain ⟨β, hβ⟩ := HypSixTypeA.exists_projAut hn hker hc
  have hβ3 : β ^ 3 = 1 := by
    ext x
    obtain ⟨u, rfl⟩ := proj_surjective (m + 1) F x
    rw [MulAut.one_apply]
    apply HypSixTypeA.projAut_pow_apply hker hc hβ 3 u u
    rw [hc3]
    group
  obtain ⟨A, σ, ε, hε, hβeq⟩ := (automorphism_generation (K := F) hn).2 β
  have hε0 : ε = 0 := HypSixTypeA.graph_exp_eq_zero hn (by decide : Odd 3) hε (by
    rw [← hβeq]
    exact hβ3)
  subst ε
  rw [pow_zero, mul_one] at hβeq
  let B : GL (Fin (m + 1)) F := (A * GeneralLinearGroup.map (σ : F →+* F) A)⁻¹
  have hsq : β * β = conjAut (m + 1) F (A * GeneralLinearGroup.map (σ : F →+* F) A) := by
    rw [hβeq, conjAut_mul_fieldAut_mul, hσsq σ, map_one, mul_one]
  have hB : conjAut (m + 1) F B = β := by
    change conjAut (m + 1) F (A * GeneralLinearGroup.map (σ : F →+* F) A)⁻¹ = β
    rw [map_inv, ← hsq]
    have h : β * (β * β) = 1 := by rw [← pow_three, hβ3]
    exact (eq_inv_of_mul_eq_one_left h).symm
  have hacts : ∀ u, c⁻¹ * ψ u * c = ψ (InnerDiagA.conjSL B u) :=
    OrdPRest.acts_of_conjAut hm hc (by
      intro u u' hu
      rw [hB]
      exact hβ u u' hu)
  have hinv : (c⁻¹, B) ∈ LinFusion.ggInducedPairs ψ := by
    intro u
    simpa only [inv_inv] using hacts u
  have hpair : (c, B⁻¹) ∈ LinFusion.ggInducedPairs ψ := by
    simpa only [Prod.inv_mk, inv_inv] using (LinFusion.ggInducedPairs ψ).inv_mem hinv
  exact LinModel.ggPsiInnerDiag_of_mem_ggInducedPairs hm hker (by decide : Odd 3) hpair hc3

theorem ggPsiInnerDiag_sl_of_cube_of_card_eq_two_or_four
    {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ} (hm : 2 ≤ m)
    (hF : Nat.card F = 2 ∨ Nat.card F = 4)
    {X : Type*} [Group X] {ψ : SpecialLinearGroup (Fin (m + 1)) F →* X}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    {c : X} (hc : c ∈ Subgroup.normalizer (ψ.range : Set X)) (hc3 : c ^ 3 = 1) :
    GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ c := by
  apply ggPsiInnerDiag_sl_of_cube_of_ringAut_sq hm _ hker hc hc3
  intro σ
  rcases hF with hF | hF
  · have hσ : σ = 1 := RingEquiv.ext fun x => by
      rcases OrthRest.eq_zero_or_eq_one_of_card_two hF x with rfl | rfl <;> simp
    rw [hσ, one_mul]
  · simpa only [pow_two] using
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256q.ringEquiv_sq_eq_one_of_card_four hF σ

end CFSG.StandardType
