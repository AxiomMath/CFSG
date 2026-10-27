module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632Lang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6D4T2Shape
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
public import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Plane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Red
public import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Class
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4TwClass
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4TwLayers
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyFG
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6D4T2Tab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShSetupE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdjDefs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import Certificates.Certificate10050
public import Certificates.Certificate8117

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem ltrb1f0b_linearMap_ext_single {τ : Tag}
    (f g : (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ))
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply LinearMap.ext
  intro v
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, h i]

private theorem ltrb1f0b_twisted_weylStep
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {τ : Tag} (S : LangSetup τ Ω 5) (hτ : Tag.E6 = τ)
    (A : (Fin τ.rank → ℤ) ≃ₗ[ℤ] (Fin τ.rank → ℤ)) (hA : ∀ v, S.ρ v = A v)
    (hΦ : ∃ (t : TwistTag) (h : t.tag = τ) (Fr : Ω →+* Ω),
        (∀ c, Fr c = c ^ S.D.q) ∧
        ∀ g, S.D.Φ g = diagramAt τ Ω t h * Units.map (entrywiseHom Fr) g *
          (diagramAt τ Ω t h)⁻¹) :
    ∃ t : WeylGroup τ,
      (∀ v : Fin τ.rank → ℤ, t • v = - A v) ∧
      (∀ w : WeylGroup τ,
        S.D.step (canonicalRep (coxeterSystem τ) Ω w) =
          canonicalRep (coxeterSystem τ) Ω (t * w * t⁻¹)) := by
  subst hτ
  obtain ⟨t, ht, Fr, hFr, hΦeq⟩ := hΦ
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
    have hS' : ∃ (t : TwistTag) (h : t.tag = Tag.E6) (Fr : Ω →+* Ω),
        (∀ c, Fr c = c ^ S.D.q) ∧
        ∀ g, S.D.Φ g = diagramAt Tag.E6 Ω t h * Units.map (entrywiseHom Fr) g *
          (diagramAt Tag.E6 Ω t h)⁻¹ := ⟨TwistTag.E6, ht, Fr, hFr, hΦeq⟩
    obtain ⟨w, hwn, hρw⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.d4t2out_rho_eq S hS'
    refine ⟨w * CFSG.LocalAnalysis.GLTheoremA.T158.e6d4t2W0, ?_, ?_⟩
    · intro v
      have hsingle : ∀ i : Fin Tag.E6.rank,
          (w * CFSG.LocalAnalysis.GLTheoremA.T158.e6d4t2W0) •
              (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = -A (Pi.single i 1) := by
        intro i
        have hroot : IsRoot Tag.E6 (Pi.single i 1 : Fin Tag.E6.rank → ℤ) :=
          isRoot_single Tag.E6 i
        rw [mul_smul, CFSG.LocalAnalysis.GLTheoremA.T158.e6d4t2_w0_smul, smul_neg,
          ← hρw _ hroot, hA]
      have hEq : A.toLinearMap =
          -(CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan Tag.E6)
            (w * CFSG.LocalAnalysis.GLTheoremA.T158.e6d4t2W0)) := by
        apply ltrb1f0b_linearMap_ext_single
        intro i
        change A (Pi.single i 1) =
          -(CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan Tag.E6)
            (w * CFSG.LocalAnalysis.GLTheoremA.T158.e6d4t2W0) (Pi.single i 1))
        rw [← smul_def, hsingle i, neg_neg]
      have h2 : A v = -((w * CFSG.LocalAnalysis.GLTheoremA.T158.e6d4t2W0) • v) := by
        have h := congrArg (fun φ : (Fin Tag.E6.rank → ℤ) →ₗ[ℤ]
            (Fin Tag.E6.rank → ℤ) => φ v) hEq
        change A v = -(CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan Tag.E6)
          (w * CFSG.LocalAnalysis.GLTheoremA.T158.e6d4t2W0) v) at h
        rw [← smul_def] at h
        exact h
      rw [h2, neg_neg]
    · intro x
      have h1 : S.D.Φ (canonicalRep (coxeterSystem Tag.E6) Ω x) =
          canonicalRep (coxeterSystem Tag.E6) Ω (e6WeylTwist x) := by
        rw [hΦeq]
        exact twistHom_canonicalRep TwistTag.E6 Ω Fr x
      change S.D.n * S.D.Φ (canonicalRep (coxeterSystem Tag.E6) Ω x) * S.D.n⁻¹ = _
      rw [h1, hwn, ← CFSG.LocalAnalysis.GLTheoremA.T158.e6d4t2_canonicalRep_conj,
        CFSG.LocalAnalysis.GLTheoremA.T158.e6d4t2_weylTwist_eq]
      congr 1
      group

theorem weylStepAt_twisted
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) (hA : RootActionAgreeAt ρ)
    (htw : ρ.row.tw = true) : WeylStepAt ρ := by
  obtain ⟨ht, hΦ⟩ := ρ.phi_twisted htw
  have hFr : ∀ c, ρ.fr c = c ^ ρ.setup.D.q := fun c => by rw [ρ.fr_eq c, ← ρ.q_eq]
  obtain ⟨t, hsmul, hstep⟩ :=
    ltrb1f0b_twisted_weylStep (S := ρ.setup) ht ρ.frobLinear hA
      ⟨TwistTag.E6, ht, ρ.fr, hFr, hΦ⟩
  refine ⟨t, ?_, hstep⟩
  intro v
  rw [htw]
  simpa using hsmul v

end CFSG.StandardType.S2MathAs1E6Companion1625

end
