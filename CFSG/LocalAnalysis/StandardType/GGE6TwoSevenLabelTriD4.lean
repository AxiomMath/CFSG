module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.RankThree.Chevalley.SteinbergBID4ThetaFixed
public import CFSG.HardMathSupport.Malle.SeitzCube.D4LayerBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.RankThree.PartOne.KE6.Phi3Field
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KE6.Phi6Torsion
public import CFSG.RankThree.PartOne.S8.Statements
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

namespace CFSG.StandardType.E6TwoSeven

open CFSG CFSG.Assembly CFSG.StandardType CFSG.RankThree.Chevalley
open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley (TwistTag)


theorem ggHasLabel_triD4_of_mulEquiv_d4ThetaFixed
    {K₀ : Type} [Field K₀] [Finite K₀] (hK₀ : Nat.card K₀ = 2)
    {Ω : Type} [Field Ω] [Algebra K₀ Ω] [IsAlgClosure K₀ Ω] [CharP Ω 2]
    {e : ℕ} (he : e = 1 ∨ e = 2) {X : Type} [Group X]
    (φ : X ≃* ↥(d4ThetaFixed Ω (iterateFrobenius Ω 2 1) e)) :
    GGHasLabel ⟨.triD4, 0, 1⟩ (X ⧸ Subgroup.center X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K₀
  let K := CFSG.RankThree.PartOne.KE6.cubicSubfield (Ω := Ω) 2 1
  have hKcard : Nat.card K = (2 ^ 1) ^ 3 := by
    dsimp only [K]
    rw [CFSG.RankThree.PartOne.KE6.natCard_cubicSubfield (Ω := Ω) (ℓ := 2) (f := 1) le_rfl]
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  have halg : Algebra.IsAlgebraic K Ω := by
    dsimp only [K]
    exact CFSG.RankThree.PartOne.KE6.isAlgebraic_cubicSubfield (Ω := Ω) (K := K₀) (ℓ := 2)
      (f := 1) (by rw [hK₀]; norm_num)
  haveI : IsAlgClosure K Ω := IsAlgClosure.mk inferInstance halg
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 1
  have hσ : ∀ c : K, σ c = c ^ 2 ^ 1 := fun c => by
    dsimp only [σ]
    rw [iterateFrobeniusEquiv_def]
  have hσhom : ∀ c : K, σ.toRingHom c = c ^ 2 ^ 1 := fun c => hσ c
  have hFr : ∀ c : Ω, iterateFrobenius Ω 2 1 c = c ^ 2 ^ 1 := fun c => by
    rw [iterateFrobenius_def]
  obtain ⟨e₁, -⟩ := CFSG.HardMathSupport.Malle.SeitzCube.exists_d4Layer_equiv
    (Ω := Ω) (K := K) (σ := σ.toRingHom) (Fr := iterateFrobenius Ω 2 1)
    (ℓ := 2) (d := 1) Nat.prime_two le_rfl hKcard he hσhom hFr
  obtain ⟨e₂⟩ := CFSG.StandardType.TableBExcSmallRest.nonempty_triD4_equiv
    (n := 1) le_rfl K hKcard σ hσ
  let eG : X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (φ.trans (CFSG.HardMathSupport.Malle.SeitzCube.d4ThetaFixedEquivLayer
      (iterateFrobenius Ω 2 1) e)).trans e₁
  let eX : X ≃* LargeEvenCenterQuot
      (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 1) :=
    eG.trans e₂.symm
  have hcenterG : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot (t := TwistTag.D4) (K := K)
      (σ := σ.toRingHom) σ.surjective
  have hZ : Subgroup.center X = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxG : eG x ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
      rw [← Subgroup.map_center_eq eG]
      exact ⟨x, hx, rfl⟩
    rw [hcenterG, Subgroup.mem_bot] at hxG
    exact eG.injective (by rw [hxG, map_one])
  refine ⟨K, inferInstance, inferInstance, hKcard, ?_⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans eX)⟩

end CFSG.StandardType.E6TwoSeven

end
