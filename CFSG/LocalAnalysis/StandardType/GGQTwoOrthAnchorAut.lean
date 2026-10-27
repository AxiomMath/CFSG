module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Defs
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1OAut
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models
import CFSG.ClassicalGroups.Orthogonal.FieldTwoTransport
import CFSG.ClassicalGroups.Orthogonal.IsometryConj
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
import CFSG.LieType.Universal.Spin.Forms
import CFSG.LieType.ChevTwo.Orthogonal
import CFSG.LieType.ChevTwo.OrthogonalBasic
import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Plane
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.Fischer.Uniq.CompTau
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
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
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
import CFSG.RankThree.PartOne.KF.ClsBasic
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
import Certificates.Certificate3006
import Certificates.Certificate3007
import Certificates.Certificate3008
import Certificates.Certificate3063
import Certificates.Certificate3077
import Certificates.Certificate3082
import Certificates.Certificate3083
import Certificates.Certificate9130

public section

namespace CFSG.StandardType.OrthAnchor

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits
open CFSG.LieType.ChevTwo CFSG.LieType.Universal.Spin CFSG.Open

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private theorem oaI_quadPlus_map {F F' : Type} [Field F] [Field F'] (φ : F ≃+* F') {n : ℕ}
    (w : Fin n ⊕ Fin n → F) :
    quadPlus n F' (fun i => φ (w i)) = φ (quadPlus n F w) := by
  simp only [quadPlus_apply, map_sum, map_mul]

private theorem oaI_quadMinus_map {F F' : Type} [Field F] [Field F'] (φ : F ≃+* F') {n : ℕ}
    (w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) :
    quadMinus n F' 1 1 (fun i => φ (w i)) = φ (quadMinus n F 1 1 w) := by
  simp only [quadMinus_apply, map_add, map_sum, map_mul, map_pow, one_mul]

private theorem oaI_two_card_no_root {F : Type} [Field F] [CharP F 2] [Fintype F]
    (hcard : Fintype.card F = 2) (s : F) : s ^ 2 + 1 * s + 1 ≠ 0 := by
  have hpow : s ^ 2 = s := by
    have h := FiniteField.pow_card (K := F) s
    rw [hcard] at h
    exact h
  rw [hpow, one_mul]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hss : s + s = 0 := by rw [← two_mul, h2, zero_mul]
  rw [hss, zero_add]
  exact one_ne_zero

theorem exists_orthogonal_conj_of_mulAut (hF : Nat.card F = 2) {m : ℕ} (hm : 2 ≤ m)
    (α : MulAut (normOmega E m)) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m),
      ∀ y : normOmega E m,
        ((α y : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) =
          g * (y : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have : FiniteDimensional F ((F × F) × (Fin m → K)) := inferInstance
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF
  have hQ := normHypForm_polarBilin_nondegenerate E m
  have h5 : 5 ≤ Module.finrank F ((F × F) × (Fin m → K)) := by
    rw [finrank_normHypForm E m]
    omega
  let v₀ : (F × F) × (Fin m → K) := ((1, 1), 0)
  have hv₀ : normHypForm E m v₀ = 1 := by
    have h0 : CFSG.ClassicalInvolution.PhanDn.Qn E m (0 : Fin m → K) = 0 :=
      QuadraticMap.map_zero (CFSG.ClassicalInvolution.PhanDn.Qn E m)
    show CFSG.Timmesfeld.ClassicalOrders.hypSum (CFSG.ClassicalInvolution.PhanDn.Qn E m)
      ((1, 1), 0) = 1
    rw [CFSG.Timmesfeld.ClassicalOrders.hypSum_apply, h0]
    norm_num
  have : Invertible (normHypForm E m v₀) :=
    invertibleOfNonzero (by rw [hv₀]; exact one_ne_zero)
  have hsO : TauCeti.QuadraticMap.reflection (normHypForm E m) v₀ ∈
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m) :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup (normHypForm E m) v₀
  have hsΩ : TauCeti.QuadraticMap.reflection (normHypForm E m) v₀ ∉
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup (normHypForm E m) hQ := by
    intro hs
    rw [CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup] at hs
    have h1 := CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ v₀
    rw [h1] at hs
    obtain ⟨k, hk⟩ := hs.2
    omega
  let φ : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime (R := F) Nat.prime_two hcard).symm
  rcases Nat.even_or_odd m with hev | hodd
  ·
    have hm3 : m ≠ 3 := by
      obtain ⟨j, hj⟩ := hev
      omega
    obtain ⟨iso⟩ := nonempty_isometryEquiv_quadPlus_of_even E hev
    let κ : (Fin (m + 1) ⊕ Fin (m + 1) → F) ≃+
        (Fin (m + 1) ⊕ Fin (m + 1) → ZMod 2) :=
      AddEquiv.piCongrRight fun _ => φ.toAddEquiv
    have hκ : ∀ w : Fin (m + 1) ⊕ Fin (m + 1) → F,
        quadPlus (m + 1) (ZMod 2) (κ w) = 0 ↔ quadPlus (m + 1) F w = 0 := by
      intro w
      have hw : κ w = fun i => φ (w i) := by
        funext i
        simp [κ]
      rw [hw, oaI_quadPlus_map φ w]
      exact map_eq_zero_iff φ φ.injective
    obtain ⟨Θ, -⟩ := CFSG.ClassicalGroups.Orthogonal.exists_mulEquiv_orthDerived_of_addEquiv
      hF (Nat.card_zmod 2) (quadPlus (m + 1) F) (quadPlus (m + 1) (ZMod 2)) κ hκ
    let e₃ : ↥(CFSG.RankThree.Classical2.orthDerived (quadPlus (m + 1) (ZMod 2))) ≃*
        ↥(StatedOmega (StatedQuadPlus (m + 1) (ZMod 2))) :=
      (CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived
        (Q := quadPlus (m + 1) (ZMod 2)) (coe_quadPlus (m + 1) (ZMod 2))).symm
    let e : ↥(normOmega E m) ≃*
        ↥(StatedOmega (StatedQuadPlus (m + 1) (ZMod 2))) :=
      ((CFSG.ClassicalGroups.Orthogonal.commutatorOrthogonalGroupCongr iso).trans Θ).trans e₃
    exact (CFSG.StandardType.QTwo.qtwoDL1_orthAut_of_equiv hF hQ h5 e
      (goodQ_plus (n := m) hm) (omegaTwoAutInduced.2 m hm hm3) hsO hsΩ).1 α
  ·
    obtain ⟨iso⟩ := nonempty_isometryEquiv_quadMinus_of_odd E hodd (b := 1) (c := 1)
      (oaI_two_card_no_root hcard)
    let κ : (Fin ((m + 1) - 1) ⊕ Fin ((m + 1) - 1) ⊕ Fin 2 → F) ≃+
        (Fin ((m + 1) - 1) ⊕ Fin ((m + 1) - 1) ⊕ Fin 2 → ZMod 2) :=
      AddEquiv.piCongrRight fun _ => φ.toAddEquiv
    have hκ : ∀ w : Fin ((m + 1) - 1) ⊕ Fin ((m + 1) - 1) ⊕ Fin 2 → F,
        quadMinus (m + 1) (ZMod 2) 1 1 (κ w) = 0 ↔ quadMinus (m + 1) F 1 1 w = 0 := by
      intro w
      have hw : κ w = fun i => φ (w i) := by
        funext i
        simp [κ]
      rw [hw, oaI_quadMinus_map φ w]
      exact map_eq_zero_iff φ φ.injective
    obtain ⟨Θ, -⟩ := CFSG.ClassicalGroups.Orthogonal.exists_mulEquiv_orthDerived_of_addEquiv
      hF (Nat.card_zmod 2) (quadMinus (m + 1) F 1 1) (quadMinus (m + 1) (ZMod 2) 1 1) κ hκ
    let e₃ : ↥(CFSG.RankThree.Classical2.orthDerived (quadMinus (m + 1) (ZMod 2) 1 1)) ≃*
        ↥(StatedOmega (StatedQuadMinus (m + 1) (ZMod 2) 1 1)) :=
      (CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived
        (Q := quadMinus (m + 1) (ZMod 2) 1 1) (coe_quadMinus (m + 1) (ZMod 2) 1 1)).symm
    let e : ↥(normOmega E m) ≃*
        ↥(StatedOmega (StatedQuadMinus (m + 1) (ZMod 2) 1 1)) :=
      ((CFSG.ClassicalGroups.Orthogonal.commutatorOrthogonalGroupCongr iso).trans Θ).trans e₃
    exact (CFSG.StandardType.QTwo.qtwoDL1_orthAut_of_equiv hF hQ h5 e
      (goodQ_minus (n := m) (by omega)) (omegaTwoAutInduced.1 m (by omega)) hsO hsΩ).1 α

end CFSG.StandardType.OrthAnchor

end
