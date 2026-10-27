module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagSpin
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models
import CFSG.HardMathSupport.Foote.E27.Q2OrthModel
import CFSG.LieType.Universal.SpinClause0
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Plane
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.Certificates.WordSubgroupRel
import CFSG.LieType.Multipliers.ProductKernel
import CFSG.LieType.Multipliers.U42Bridge
import CFSG.LieType.Multipliers.U43Action
import CFSG.LieType.Multipliers.U43BridgeInputs
import CFSG.LieType.Multipliers.U62Action
import CFSG.LieType.Multipliers.U62Bridge
import CFSG.LieType.Multipliers.U62Kernel
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
import CFSG.Monster.B.Classical.PlaneAut
import CFSG.Monster.B.TwoA.Amalgam.Data
import CFSG.Monster.B.TwoA.Sp8.Par1
import CFSG.Monster.B.TwoA.Unitary.LinThree
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.KF.ClsBasic
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.Sporadic.SmallOddCore.CheckSpec
import CFSG.YGroups.Y322Central
import Certificates.Certificate10005
import Certificates.Certificate10006
import Certificates.Certificate10007
import Certificates.Certificate10008
import Certificates.Certificate10009
import Certificates.Certificate10010
import Certificates.Certificate10012
import Certificates.Certificate10013
import Certificates.Certificate10014
import Certificates.Certificate10016
import Certificates.Certificate10018
import Certificates.Certificate12041
import Certificates.Certificate12042
import Certificates.Certificate12043
import Certificates.Certificate12044
import Certificates.Certificate12045
import Certificates.Certificate12046
import Certificates.Certificate16015
import Certificates.Certificate16040
import Certificates.Certificate2154
import Certificates.Certificate2157
import Certificates.Certificate2267
import Certificates.Certificate2326
import Certificates.Certificate3006
import Certificates.Certificate3007
import Certificates.Certificate3008
import Certificates.Certificate3063
import Certificates.Certificate3077
import Certificates.Certificate3082
import Certificates.Certificate3083
import Certificates.Certificate9130

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
  CFSG.HardMathSupport.Foote.E27

private theorem admissible_POmegaPlus_one {m : ℕ} (hm : 4 ≤ m) :
    StatedLieAdmissible .POmegaPlus m 2 1 :=
  ⟨Nat.prime_two, le_rfl, hm⟩

private theorem bnRank_POmegaPlus_three {m : ℕ} (hm : 4 ≤ m) :
    3 ≤ bnRank .POmegaPlus m := by
  rw [bnRank]
  omega

private theorem admissible_POmegaMinus_one {m : ℕ} (hm : 4 ≤ m) :
    StatedLieAdmissible .POmegaMinus m 2 1 :=
  ⟨Nat.prime_two, le_rfl, hm⟩

private theorem bnRank_POmegaMinus_three {m : ℕ} (hm : 4 ≤ m) :
    3 ≤ bnRank .POmegaMinus m := by
  rw [bnRank]
  omega

section Tag

variable {G : Type} [Group G]

theorem ker_le_center_of_range_ne_bot_POmegaPlus {m f : ℕ} (hm : 3 ≤ m)
    (ψ : (ggU .POmegaPlus m f).K →* G) (hne : ψ.range ≠ ⊥) :
    ψ.ker ≤ Subgroup.center (ggU .POmegaPlus m f).K := by
  have hU : ggU .POmegaPlus m f =
      ⟨spinGroup (quadPlus m (GaloisField 2 f)), plusDatum m (GaloisField 2 f) hm⟩ := by
    simp only [ggU, lieUniversal, hm, ↓reduceDIte]
  have hq : IsQuasisimple (ggU .POmegaPlus m f).K := by
    rw [hU]
    exact isQuasisimple_spinGroup_quadPlus (K := GaloisField 2 f) hm
  have hφ : ∃ k, ψ k ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (MonoidHom.range_eq_bot_iff.mpr (MonoidHom.ext h))
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hφ

theorem ker_le_center_of_range_ne_bot_POmegaMinus {m f : ℕ} (hm : 4 ≤ m)
    (ψ : (ggU .POmegaMinus m f).K →* G) (hne : ψ.range ≠ ⊥) :
    ψ.ker ≤ Subgroup.center (ggU .POmegaMinus m f).K := by
  have hU : ggU .POmegaMinus m f =
      ⟨spinGroup (quadMinus m (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
        minusDatum m (minusCoeffs_irr 2 f)⟩ := rfl
  have hq : IsQuasisimple (ggU .POmegaMinus m f).K := by
    rw [hU]
    exact isQuasisimple_spinGroup_quadMinus (K := GaloisField 2 f)
      (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2) hm (minusCoeffs_irr 2 f)
  have hφ : ∃ k, ψ k ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (MonoidHom.range_eq_bot_iff.mpr (MonoidHom.ext h))
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hφ

variable [Finite G]

theorem ggSecFiveData_of_psi_POmegaPlus_one {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {m : ℕ} (hm : 4 ≤ m)
    (ψ : (ggU .POmegaPlus m 1).K →* G)
    (hrange : ψ.range = ggG0 p B x L D J) (hne : ggG0 p B x L D J ≠ ⊥) :
    GGSecFiveData p B x L D J := by
  have hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus m 1).K :=
    ker_le_center_of_range_ne_bot_POmegaPlus (m := m) (f := 1) (by omega) ψ (by rwa [hrange])
  exact Or.inr (Or.inr ⟨.POmegaPlus, m, 1,
    ggSecFivePres_of_psi_POmegaPlus (admissible_POmegaPlus_one hm)
      (bnRank_POmegaPlus_three hm) ψ hker hrange⟩)

theorem ggSecFiveData_of_psi_POmegaMinus_one {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {m : ℕ} (hm : 4 ≤ m)
    (ψ : (ggU .POmegaMinus m 1).K →* G)
    (hrange : ψ.range = ggG0 p B x L D J) (hne : ggG0 p B x L D J ≠ ⊥) :
    GGSecFiveData p B x L D J := by
  have hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus m 1).K :=
    ker_le_center_of_range_ne_bot_POmegaMinus (m := m) (f := 1) hm ψ (by rwa [hrange])
  exact Or.inr (Or.inr ⟨.POmegaMinus, m, 1,
    ggSecFivePres_of_psi_POmegaMinus (admissible_POmegaMinus_one hm)
      (bnRank_POmegaMinus_three hm) ψ hker hrange⟩)

theorem ggSecFiveData_of_psi_POmegaPlus {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {m f : ℕ} (hadm : StatedLieAdmissible .POmegaPlus m 2 f)
    (hrank : 3 ≤ bnRank .POmegaPlus m) (ψ : (ggU .POmegaPlus m f).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus m f).K)
    (hrange : ψ.range = ggG0 p B x L D J) :
    GGSecFiveData p B x L D J :=
  Or.inr (Or.inr ⟨.POmegaPlus, m, f,
    ggSecFivePres_of_psi_POmegaPlus hadm hrank ψ hker hrange⟩)

theorem ggSecFiveData_of_psi_POmegaMinus {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {m f : ℕ} (hadm : StatedLieAdmissible .POmegaMinus m 2 f)
    (hrank : 3 ≤ bnRank .POmegaMinus m) (ψ : (ggU .POmegaMinus m f).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus m f).K)
    (hrange : ψ.range = ggG0 p B x L D J) :
    GGSecFiveData p B x L D J :=
  Or.inr (Or.inr ⟨.POmegaMinus, m, f,
    ggSecFivePres_of_psi_POmegaMinus hadm hrank ψ hker hrange⟩)

theorem ggSecFiveData_of_injective_normOmega_of_card_two {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {F K : Type} [Field F] [Field K] [Algebra F K]
    [Finite K] [CharP K 2] {f n : ℕ}
    (E : QuadExt F K (unitaryInvolution K 2 f))
    (hF : Nat.card F = 2) (hn : 3 ≤ n)
    (Ψ : normOmega E n →* G) (hΨ : Function.Injective Ψ)
    (hrange : Ψ.range = ggG0 p B x L D J) :
    GGSecFiveData p B x L D J := by
  letI : Finite F := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hF₀ : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 (by decide)
  let σ : F ≃+* GaloisField 2 1 :=
    FiniteField.ringEquivOfCardEq (by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF, hF₀])
  have h2 : (2 : GaloisField 2 1) = 0 := CharP.cast_eq_zero (GaloisField 2 1) 2
  rcases Nat.even_or_odd n with hne | hno
  ·
    obtain ⟨eN⟩ := nonempty_normOmega_mulEquiv_plus E hne
    let eField : ↥(StatedOmega (StatedQuadPlus (n + 1) F)) ≃*
        ↥(StatedOmega (StatedQuadPlus (n + 1) (GaloisField 2 1))) :=
      Q2.statedOmegaEquiv σ _ _ (by
        intro v
        simp only [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, map_sum, map_mul])
    let eSpin := spinEquivCommutatorQuadPlus (n := n + 1) (K := GaloisField 2 1) (by omega) h2
    let eD := (CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived
      (Q := quadPlus (n + 1) (GaloisField 2 1))
      (coe_quadPlus (n + 1) (GaloisField 2 1))).symm
    have hU : ggU .POmegaPlus (n + 1) 1 =
        ⟨spinGroup (quadPlus (n + 1) (GaloisField 2 1)),
          plusDatum (n + 1) (GaloisField 2 1) (by omega)⟩ := by
      simp only [ggU, lieUniversal, show 3 ≤ n + 1 by omega, ↓reduceDIte]
    let eS : (ggU .POmegaPlus (n + 1) 1).K ≃* normOmega E n := by
      rw [hU]
      exact eSpin.trans (eD.trans (eField.symm.trans eN.symm))
    let ψ : (ggU .POmegaPlus (n + 1) 1).K →* G := Ψ.comp eS.toMonoidHom
    have hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus (n + 1) 1).K := by
      rw [(MonoidHom.ker_eq_bot_iff ψ).mpr (hΨ.comp eS.injective)]
      exact bot_le
    have hψrange : ψ.range = ggG0 p B x L D J := by
      dsimp [ψ]
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eS.surjective,
        ← MonoidHom.range_eq_map, hrange]
    exact ggSecFiveData_of_psi_POmegaPlus (m := n + 1) (f := 1)
      (admissible_POmegaPlus_one (by omega)) (bnRank_POmegaPlus_three (by omega)) ψ hker hψrange
  ·
    let b₀ : GaloisField 2 1 := (minusCoeffs 2 1).1
    let c₀ : GaloisField 2 1 := (minusCoeffs 2 1).2
    have hirr : ∀ s : F, s ^ 2 + (σ.symm b₀) * s + (σ.symm c₀) ≠ 0 := by
      intro s hs
      apply minusCoeffs_irr 2 1 (σ s)
      simpa only [b₀, c₀, map_add, map_mul, map_pow, map_zero,
        RingEquiv.apply_symm_apply] using congrArg σ hs
    obtain ⟨eN⟩ := nonempty_normOmega_mulEquiv_minus E hno hirr
    let eField : ↥(StatedOmega (StatedQuadMinus (n + 1) F (σ.symm b₀) (σ.symm c₀))) ≃*
        ↥(StatedOmega (StatedQuadMinus (n + 1) (GaloisField 2 1) b₀ c₀)) :=
      Q2.statedOmegaEquiv σ _ _ (by
        intro v
        simp only [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, map_sum, map_add, map_mul,
          map_pow, b₀, c₀, RingEquiv.apply_symm_apply])
    let eSpin := spinEquivCommutatorQuadMinus (n := n + 1) (K := GaloisField 2 1)
      (b := b₀) (c := c₀) (by omega) (by simpa [b₀, c₀] using minusCoeffs_irr 2 1) h2
    let eD := (CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived
      (Q := quadMinus (n + 1) (GaloisField 2 1) b₀ c₀)
      (coe_quadMinus (n + 1) (GaloisField 2 1) b₀ c₀)).symm
    have hU : ggU .POmegaMinus (n + 1) 1 =
        ⟨spinGroup (quadMinus (n + 1) (GaloisField 2 1) (minusCoeffs 2 1).1
            (minusCoeffs 2 1).2),
          Twisted.minusDatum (n + 1) (minusCoeffs_irr 2 1)⟩ := rfl
    let eS : (ggU .POmegaMinus (n + 1) 1).K ≃* normOmega E n := by
      rw [hU]
      exact eSpin.trans (eD.trans (eField.symm.trans eN.symm))
    let ψ : (ggU .POmegaMinus (n + 1) 1).K →* G := Ψ.comp eS.toMonoidHom
    have hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus (n + 1) 1).K := by
      rw [(MonoidHom.ker_eq_bot_iff ψ).mpr (hΨ.comp eS.injective)]
      exact bot_le
    have hψrange : ψ.range = ggG0 p B x L D J := by
      dsimp [ψ]
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eS.surjective,
        ← MonoidHom.range_eq_map, hrange]
    exact ggSecFiveData_of_psi_POmegaMinus (m := n + 1) (f := 1)
      (admissible_POmegaMinus_one (by omega)) (bnRank_POmegaMinus_three (by omega)) ψ hker hψrange

end Tag

end CFSG.StandardType

end
