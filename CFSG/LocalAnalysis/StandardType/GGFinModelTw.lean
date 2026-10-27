module

public import CFSG.LocalAnalysis.StandardType.GGFinModelPkg
public import CFSG.LocalAnalysis.StandardType.GGFinModelTwCent
public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LieType.Steinberg.Exceptional.Fields
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtTwE6
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
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
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
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
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Twisted

private theorem center_le_ker_of_surjective_aux {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (hH : Subgroup.center H = ⊥) : Subgroup.center G ≤ f.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hzH : f z ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hf y
    have h := congrArg f (Subgroup.mem_center_iff.1 hz x)
    rwa [map_mul, map_mul] at h
  rw [hH] at hzH
  simpa using hzH

noncomputable def ggKbEquivTwE6 (n f : ℕ) (hf : 1 ≤ f) :
    GGKb .twistedE6 n f ≃*
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) := by
  classical
  let F := GaloisField 2 (2 * f)
  let σ : F →+* F := frobQ 2 f
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup (ModGL TwistTag.E6.tag F) := twistedFixedGroup TwistTag.E6 F σ
  let C : Subgroup (ModGL TwistTag.E6.tag F) := graphFixedRootGroup TwistTag.E6 F σ
  let K : Type := twistedE6Group 2 f
  let φ : K →* ↥⁅R, R⁆ := twistedE6Isogeny 2 f hf
  change K ⧸ Subgroup.center K ≃* ↥C
  have hσsurj : Function.Surjective σ :=
    Finite.surjective_of_injective (frobQ 2 f).injective
  have hφsurj : Function.Surjective φ := twistedE6Isogeny_surjective (p := 2) (f := f) hf
  have hhK : Nat.card F = (2 ^ f) ^ TwistTag.E6.order := by
    rw [show TwistTag.E6.order = 2 from rfl]
    exact card_galoisField_two_mul 2 f hf
  have hΓ : ⁅R, R⁆ = C :=
    (finite_fixed_root_group_perfect (p := 2) (f := f) TwistTag.E6 Nat.prime_two hf F hhK σ
      (frobQ_apply 2 f)).2.2.1
  have hcenterC : Subgroup.center ↥C = ⊥ :=
    center_graphFixedRootGroup_eq_bot (t := TwistTag.E6) (K := F) (σ := σ) hσsurj
  have hcenterR : Subgroup.center ↥⁅R, R⁆ = ⊥ := by
    rw [← Subgroup.map_center_eq (MulEquiv.subgroupCongr hΓ.symm), hcenterC, Subgroup.map_bot]
  have hker_le : φ.ker ≤ Subgroup.center K := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have h1 : e6IsogenyT F (g : e6Data_valid.minGroup F) = 1 := by
      apply Subtype.ext
      have h2 : ((e6IsogenyT F (g : e6Data_valid.minGroup F) :
            ↥(adjointGroup TwistTag.E6.tag F)) : ModGL TwistTag.E6.tag F) = 1 := by
        have hg' := congrArg (fun y : ↥⁅R, R⁆ => (y : ModGL TwistTag.E6.tag F)) hg
        rw [coe_twistedE6Isogeny (p := 2) (f := f) hf g, OneMemClass.coe_one] at hg'
        exact hg'
      simpa using h2
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1
      ((ker_e6IsogenyT_le_center F) (MonoidHom.mem_ker.2 h1)) (h : e6Data_valid.minGroup F)
  have hcenter_le : Subgroup.center K ≤ φ.ker :=
    center_le_ker_of_surjective_aux φ hφsurj hcenterR
  have hker : φ.ker = Subgroup.center K := le_antisymm hker_le hcenter_le
  exact (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).trans
      (MulEquiv.subgroupCongr hΓ))

theorem ggKbEquivTwE6_mk (n f : ℕ) (hf : 1 ≤ f) (k : (ggU .twistedE6 n f).K) :
    ((ggKbEquivTwE6 n f hf (QuotientGroup.mk k) :
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((twistedE6Isogeny 2 f hf k : ↥⁅twistedFixedGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f), twistedFixedGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) := by
  unfold ggKbEquivTwE6
  rfl

theorem ggLangPkg_twE6_adjoint {f : ℕ} (hf : 1 ≤ f) (D : LangDatum Tag.E6 GGL)
    (hΦ : D.Φ = twistHom TwistTag.E6 GGL (ggFrobT f)) :
    GGLangPkg D ((baseChangeGL (ggRatEmb (2 * f))).comp
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype) := by
  classical
  let F := GaloisField 2 (2 * f)
  let σ : F →+* F := frobQ 2 f
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra F GGL := (ggRatEmb (2 * f)).toAlgebra
  haveI : IsScalarTower (ZMod 2) F GGL := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : Algebra.IsAlgebraic F GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := F) (A := GGL)
  haveI : IsAlgClosure F GGL := ⟨IsAlgClosure.isAlgClosed (ZMod 2), inferInstance⟩
  have hσsurj : Function.Surjective σ :=
    Finite.surjective_of_injective (frobQ 2 f).injective
  let σE : F ≃+* F := RingEquiv.ofBijective σ ⟨σ.injective, hσsurj⟩
  have hσE : ∀ c, σE c = c ^ (2 ^ f) := fun c => by
    change frobQ 2 f c = c ^ (2 ^ f)
    exact frobQ_apply 2 f c
  let ι : ↥(twistedE6RootGroup F σE) →* ModGL Tag.E6 GGL :=
    (baseChangeGL (algebraMap F GGL)).comp (twistedE6RootGroup F σE).subtype
  change GGLangPkg D ι
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (baseChangeGL_injective (algebraMap F GGL)).comp (Subgroup.subtype_injective _)
  · exact langDescent_twE6 (ℓ := 2) (f := f) (K := F) (L := GGL) (Fr := ggFrobT f) (p := 5)
      Nat.prime_two hf (card_galoisField_two_mul 2 f hf) σE hσE
      (ggFrobT_apply f) D hΦ Nat.prime_five (by norm_num)
  · intro z hz hc
    refine ggTwCentTriv (K := F) (L := GGL) σ hσsurj (ggRatEmb (2 * f)) hz ?_
    rintro h ⟨y, hy, rfl⟩
    exact hc ⟨y, hy⟩
  · let R : Subgroup (ModGL TwistTag.E6.tag GGL) := twistedFixedGroup TwistTag.E6 GGL (ggFrobT f)
    let C : Subgroup (ModGL TwistTag.E6.tag GGL) :=
      (graphFixedRootGroup TwistTag.E6 F σ).map (baseChangeGL (algebraMap F GGL))
    have hcard_R : Nat.card R = CFSG.SeitzReduction.E6Pilot.numTwistedE6 (2 ^ f) := by
      have h := (CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
        (ℓ := 2) (f := f) Nat.prime_two hf F (card_galoisField_two_mul 2 f hf) σ
        (frobQ_apply 2 f) GGL (ggFrobT f) (ggFrobT_apply f)).2.2.2.2.2.1
      simpa only [R, CFSG.SeitzReduction.E6Pilot.numTwistedE6] using h
    have hder : ⁅R, R⁆ = C := by
      have h := (CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
        (ℓ := 2) (f := f) Nat.prime_two hf F (card_galoisField_two_mul 2 f hf) σ
        (frobQ_apply 2 f) GGL (ggFrobT f) (ggFrobT_apply f)).2.2.1
      simpa only [R, C] using h
    have hrange : ι.range = C := by
      change ((baseChangeGL (algebraMap F GGL)).comp
        (twistedE6RootGroup F σE).subtype).range = C
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rfl
    have hfixD : D.fix = R := by
      ext x
      rw [LangDatum.mem_fix, hΦ]
      rfl
    rw [hrange, hfixD]
    have hC0card : Nat.card (graphFixedRootGroup TwistTag.E6 F σ) = ordTwistedE6 (2 ^ f) :=
      CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 (K := F) Nat.prime_two hf
        (card_galoisField_two_mul 2 f hf) σ (frobQ_apply 2 f)
    have hCcard : Nat.card C = Nat.card (graphFixedRootGroup TwistTag.E6 F σ) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective (algebraMap F GGL))
    have hnum : Nat.card (graphFixedRootGroup TwistTag.E6 F σ) * Nat.gcd 3 (2 ^ f + 1) =
        CFSG.SeitzReduction.E6Pilot.numTwistedE6 (2 ^ f) := by
      rw [hC0card]
      exact CFSG.SeitzReduction.E6Pilot.ordTwistedE6_mul_gcd (2 ^ f)
    have hle : C ≤ R := by
      rw [← hder]
      simpa using Subgroup.commutator_le_sup (H₁ := R) (H₂ := R)
    have hrel : C.relIndex R * Nat.card ↥(C ⊓ R) = Nat.card R :=
      Subgroup.relIndex_mul_card (H := C) (K := R)
    have hinf : C ⊓ R = C := inf_eq_left.mpr hle
    have hkey : C.relIndex R * Nat.card C = Nat.card R := by
      rw [← hrel, hinf]
    have hkey2 : C.relIndex R * Nat.card (graphFixedRootGroup TwistTag.E6 F σ) =
        CFSG.SeitzReduction.E6Pilot.numTwistedE6 (2 ^ f) := by
      rw [← hCcard, hkey, hcard_R]
    have hC0pos : 0 < Nat.card (graphFixedRootGroup TwistTag.E6 F σ) := Nat.card_pos
    have hrel_eq : C.relIndex R * Nat.card (graphFixedRootGroup TwistTag.E6 F σ) =
        Nat.gcd 3 (2 ^ f + 1) * Nat.card (graphFixedRootGroup TwistTag.E6 F σ) := by
      rw [hkey2, ← hnum, mul_comm]
    have hindex : C.relIndex R = Nat.gcd 3 (2 ^ f + 1) :=
      Nat.eq_of_mul_eq_mul_right hC0pos hrel_eq
    calc C.relIndex R = Nat.gcd 3 (2 ^ f + 1) := hindex
      _ ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (2 ^ f + 1))

end Twisted

end CFSG.StandardType.GGFinModel
