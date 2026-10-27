module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR4
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.LieType.Chevalley.E6SecondGraphFixedSubgroup
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType.TwE6OuterGen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.SeitzReduction.TwistedE6Pilot

theorem apply_eq_self_of_commute_conj {H : Type*} [Group H] (hZ : Subgroup.center H = ⊥)
    {t : MulAut H} {c : H} (h : t * MulAut.conj c = MulAut.conj c * t) : t c = c :=
  CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot hZ (by
    rw [← CFSG.LieType.Chevalley.mulAut_mul_conj_mul_inv t c, h, mul_inv_cancel_right])


private theorem etaAut_apply_eq_of_xiAut_apply_eq {f : ℕ} (hf : 1 ≤ f) {k K : Type} [Field k]
    [Field K] [Algebra k K] [CharP K 2] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (x : ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (hx : xiAut σ (apply_apply_eq hK hσ) x = x) :
    etaAut σ (apply_apply_eq hK hσ) x = x := by
  obtain ⟨-, -, -, -, -, ⟨e₂, -, -, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf k K hk hK σ hσ
  obtain ⟨htJ, hJC', η₀, hη₀, -, -, -, hfixξ, -, -, -, -⟩ := hsec
  obtain ⟨-, ⟨⟨η', hη', -, -, hfixJ, -⟩, -, -⟩⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σ hσ
  have hη₀e : η₀ = etaAut σ (apply_apply_eq hK hσ) :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hη₀, coe_etaAut])
  have hη'e : η' = etaAut σ (apply_apply_eq hK hσ) :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hη', coe_etaAut])
  have hξe : MulAut.conj (⟨_, hJC' htJ⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ)) * η₀ =
      xiAut σ (apply_apply_eq hK hσ) := by
    rw [hη₀e]
    rfl
  have hxfix : (MulAut.conj (⟨_, hJC' htJ⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ)) *
      η₀) x = x := by
    rw [hξe]
    exact hx
  have hxJ : (x : ModGL TwistTag.E6.tag K) ∈
      (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)) :=
    ((hfixξ x).1 hxfix).1
  have hfix' : η' x = x := (hfixJ x).2 hxJ
  rwa [hη'e] at hfix'

theorem exists_aut_etaAut_apply_eq {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : MulAut (graphFixedRootGroup TwistTag.E6 K σ)} (ht2 : t ^ 2 = 1)
    (htI : t ∉ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ →*
      MulAut (graphFixedRootGroup TwistTag.E6 K σ)).range) :
    ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
      ∀ y, t y = y → etaAut σ (apply_apply_eq hK hσ) (φ y) = φ y := by
  have hfix : ∀ φ t' : MulAut (graphFixedRootGroup TwistTag.E6 K σ), φ * t * φ⁻¹ = t' →
      ∀ y, t y = y → t' (φ y) = φ y := by
    intro φ t' h y hy
    rw [← h, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hy]
  rcases (conj_etaAut_or_xiAut_of_outer hf hK σ hσ).1 t ht2 htI with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · exact ⟨φ, hfix φ _ hφ⟩
  · refine ⟨φ, fun y hy => ?_⟩
    have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK
    letI : Algebra (GaloisField 2 f) K := ι.toAlgebra
    exact etaAut_apply_eq_of_xiAut_apply_eq hf hk hK σ hσ (φ y) (hfix φ _ hφ y hy)

theorem fieldActor_commute_etaAut {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) (δ : K ≃+* K) :
    fieldActor σ σ = etaAut σ.toRingHom (apply_apply_eq hK hσ) ∧
      Commute (fieldActor σ δ) (fieldActor (t := TwistTag.E6) σ σ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hfield, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  refine ⟨MulEquiv.ext fun y => Subtype.ext (by rw [hfield, coe_etaAut]), ?_⟩
  have hδσ : δ * σ = σ * δ :=
    RingEquiv.ext fun c => show δ (σ c) = σ (δ c) by rw [hσ, hσ, map_pow]
  show fieldActor σ δ * fieldActor σ σ = fieldActor σ σ * fieldActor σ δ
  rw [← fieldActor_mul, ← fieldActor_mul, hδσ]

theorem exists_inndiag_diagramMap_commute {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : MulAut (twistedE6RootGroup K σ)} (ht2 : t ^ 2 = 1)
    (htI : t ∉ (twistedE6InndiagConj K σ).range) :
    ∃ c : twistedE6InndiagGL K σ, ∀ y : twistedE6RootGroup K σ, t y = y →
      diagramMap TwistTag.E6 K * ((c : ModGL TwistTag.E6.tag K) * y *
        (c : ModGL TwistTag.E6.tag K)⁻¹) = (c : ModGL TwistTag.E6.tag K) * y *
          (c : ModGL TwistTag.E6.tag K)⁻¹ * diagramMap TwistTag.E6 K := by
  haveI : CharP K 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hK
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f := hσ
  have htI' : t ∉ (MulAut.conj : twistedE6RootGroup K σ →*
      MulAut (twistedE6RootGroup K σ)).range := fun h =>
    htI (by rw [range_twistedE6InndiagConj]; exact Subgroup.mem_sup_left h)
  obtain ⟨φ, hφ⟩ := exists_aut_etaAut_apply_eq hf hK σ.toRingHom hσ' ht2 htI'
  obtain ⟨-, -, -, -, -, -, -, hdec, ⟨Θ, -, -, hker, -⟩, hfield, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  obtain ⟨g, u, δ, hφd⟩ := hdec φ
  obtain ⟨hη, hcomm⟩ := fieldActor_commute_etaAut hf hK σ hσ δ
  have hψ : (fieldActor σ δ)⁻¹ * φ ∈ (twistedE6InndiagConj K σ).range := by
    have h1 : MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u ∈ Θ.ker := by
      rw [hker]
      exact mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right ⟨u, rfl⟩)
    have h2 := (MonoidHom.normal_ker Θ).conj_mem _ h1 (fieldActor σ δ)⁻¹
    have h3 : (fieldActor σ δ)⁻¹ * (MulAut.conj g *
        compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ δ) =
        (fieldActor σ δ)⁻¹ * (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u) *
          (fieldActor σ δ)⁻¹⁻¹ := by group
    rw [range_twistedE6InndiagConj, ← hker, hφd, h3]
    exact h2
  obtain ⟨c, hc⟩ := hψ
  refine ⟨c, fun y hy => ?_⟩
  have h1 : fieldActor σ σ (φ y) = φ y := by rw [hη]; exact hφ y hy
  have hfix : fieldActor σ σ (twistedE6InndiagConj K σ c y) = twistedE6InndiagConj K σ c y := by
    rw [hc]
    calc fieldActor σ σ (((fieldActor σ δ)⁻¹ * φ : MulAut (twistedE6RootGroup K σ)) y)
        = (fieldActor σ σ * (fieldActor σ δ)⁻¹ : MulAut (twistedE6RootGroup K σ)) (φ y) := rfl
      _ = ((fieldActor σ δ)⁻¹ * fieldActor σ σ : MulAut (twistedE6RootGroup K σ)) (φ y) := by
          rw [← hcomm.inv_left.eq]
      _ = (fieldActor σ δ)⁻¹ (fieldActor σ σ (φ y)) := rfl
      _ = ((fieldActor σ δ)⁻¹ * φ : MulAut (twistedE6RootGroup K σ)) y := by rw [h1]; rfl
  have hfix' := congrArg Subtype.val hfix
  rw [hfield, twistedE6InndiagConj_apply] at hfix'
  calc diagramMap TwistTag.E6 K * ((c : ModGL TwistTag.E6.tag K) * y *
        (c : ModGL TwistTag.E6.tag K)⁻¹) =
      diagramMap TwistTag.E6 K * ((c : ModGL TwistTag.E6.tag K) * y *
        (c : ModGL TwistTag.E6.tag K)⁻¹) * (diagramMap TwistTag.E6 K)⁻¹ *
          diagramMap TwistTag.E6 K := by group
    _ = (c : ModGL TwistTag.E6.tag K) * y * (c : ModGL TwistTag.E6.tag K)⁻¹ *
        diagramMap TwistTag.E6 K := by rw [hfix']

end CFSG.StandardType.TwE6OuterGen

end
