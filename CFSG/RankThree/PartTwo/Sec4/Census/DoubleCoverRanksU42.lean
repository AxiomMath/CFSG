module

public import CFSG.RankThree.PartTwo.Census.TransitiveLift
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.LieType.Multipliers.U42
public import CFSG.RankThree.SubgroupLists.SymplecticInvolutions
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.GH74.Generic.S3.L3Cover
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherProjective
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.GH74.Generic.S3.LeavesFine
public import CFSG.GH74.Generic.S3.Lem37
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
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
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Open.QuasithinDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
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
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3085Base
public import Certificates.Certificate3951
public import Certificates.Certificate8171
public import Certificates.Certificate9130
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

namespace DoubleCoverRanksTwo

open CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LocalAnalysis.ComponentInitial

theorem card_le_four_of_isElementaryAbelian {B : Subgroup (StatedSp 2 (ZMod 3))}
    (hB : CFSG.IsElementaryAbelian 2 B) : Nat.card B ≤ 4 := by
  classical
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  let f : B → GL (Fin 2 ⊕ Fin 2) (ZMod 3) := fun b => ((b : StatedSp 2 (ZMod 3)) :
    GL (Fin 2 ⊕ Fin 2) (ZMod 3))
  have hf : Function.Injective f := fun b b' h => Subtype.ext (Subtype.ext h)
  have := hB
  have hsq : ∀ b : B, f b * f b = 1 := fun b => by
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B)
      (b : StatedSp 2 (ZMod 3)) b.2
    have h' := congrArg Subtype.val h
    simpa [f, sq] using h'
  have hcomm : ∀ b b' : B, f b * f b' = f b' * f b := fun b b' => by
    have h := hB.is_comm.comm b b'
    have h' := congrArg (fun x : B => ((x : StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3))) h
    simpa [f] using h'
  have hmem : ∀ b : B, f b ∈ StatedSp 2 (ZMod 3) := fun b => (b : StatedSp 2 (ZMod 3)).2
  obtain ⟨a, ha⟩ : ∃ a : GL (Fin 2 ⊕ Fin 2) (ZMod 3),
      ∀ b : B, f b ∈ ({1, -1, a, -a} : Finset (GL (Fin 2 ⊕ Fin 2) (ZMod 3))) := by
    by_cases hall : ∀ b : B, f b = 1 ∨ f b = -1
    · refine ⟨1, fun b => ?_⟩
      rcases hall b with h | h <;> simp [h]
    · push Not at hall
      obtain ⟨b₀, hb₁, hbm⟩ := hall
      refine ⟨f b₀, fun b => ?_⟩
      rcases CFSG.RankThree.SubgroupLists.eq_of_commute_involution h2 (hmem b₀) (hmem b)
          (hsq b₀) (hsq b) (hcomm b₀ b) hb₁ hbm with h | h | h | h <;> simp [h]
  calc Nat.card B ≤ Nat.card ({1, -1, a, -a} : Finset (GL (Fin 2 ⊕ Fin 2) (ZMod 3))) :=
        Nat.card_le_card_of_injective (fun b => ⟨f b, ha b⟩)
          (fun b b' h => hf (Subtype.mk.inj h))
    _ = ({1, -1, a, -a} : Finset (GL (Fin 2 ⊕ Fin 2) (ZMod 3))).card :=
        Nat.card_eq_finsetCard _
    _ ≤ 4 := Finset.card_le_four

theorem pRank_le_two_of_mulEquiv {J : Type} [Group J] (α : StatedSp 2 (ZMod 3) ≃* J) :
    CFSG.pRank 2 J ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine csSup_le' ?_
  rintro r ⟨A, hA, hcard⟩
  have hB : CFSG.IsElementaryAbelian 2 (A.map α.symm.toMonoidHom) := CFSG.IsElementaryAbelian.map _
  have hcB : Nat.card (A.map α.symm.toMonoidHom) = 2 ^ r := by
    rw [Subgroup.card_map_of_injective α.symm.injective, hcard]
  have h4 := card_le_four_of_isElementaryAbelian hB
  rw [hcB] at h4
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (h4.trans (by norm_num))

theorem blueprint_lieModel_projSU_four_two :
    CFSG.Blueprint.LieModel (projSU 4 2 1) .PSU 4 2 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact blueprint_lieModel_of_classical (by decide)
    (lieModel_projSU (n := 4) (p := 2) (e := 1) ⟨Nat.prime_two, le_rfl, by decide⟩)

theorem nonempty_mulEquiv_statedSp_of_double_cover
    {J : Type} [Group J] [Finite J] (hJ : Group.IsPerfect J)
    (hZ : Nat.card (Subgroup.center J) = 2) (e : J ⧸ Subgroup.center J ≃* projSU 4 2 1) :
    Nonempty (StatedSp 2 (ZMod 3) ≃* J) := by
  have hm := blueprint_lieModel_projSU_four_two
  obtain ⟨e43⟩ := CFSG.LieType.Multipliers.U42.nonempty_mulEquiv_PSp43 hm
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two _ hm
  set Z := SymplecticHigher.spScalars 2 (ZMod 3)
  let p₀ : StatedSp 2 (ZMod 3) →* projSU 4 2 1 := e43.symm.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hp₀ : Function.Surjective p₀ := e43.symm.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker₀ : p₀.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker]
    change e43.symm (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff e43.symm e43.symm.injective, QuotientGroup.eq_one_iff]
  have hk₀ : p₀.ker ≤ Subgroup.center (StatedSp 2 (ZMod 3)) :=
    hker₀ ▸ SymplecticHigher.spScalars_le_center
  have hcard₀ : Nat.card p₀.ker = 2 := by
    rw [hker₀, card_spScalars_eq_gcd (ZMod 3) (r := 2) (by norm_num), Nat.card_zmod]
    norm_num
  have hS₀ : Group.IsPerfect (StatedSp 2 (ZMod 3)) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 (ZMod 3)
      (Or.inr (Or.inl ⟨Nat.card_zmod 3, le_rfl⟩))
  let p : J →* projSU 4 2 1 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : p.ker = Subgroup.center J := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have hM : Nat.card (hopfMultiplier (projSU 4 2 1)) = Nat.card p₀.ker := by
    rw [hcard₀, ← Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv, Nat.card_congr eM.toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  obtain ⟨α, hα, -⟩ := CFSG.GH74.Generic.S3.exists_lift_of_card_eq hS₀ hJ p₀ hp₀ hk₀ p hp
    hker.le hM
  have hc₀ : Nat.card (StatedSp 2 (ZMod 3)) = Nat.card (projSU 4 2 1) * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup p₀.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective p₀ hp₀).toEquiv, hcard₀]
  have hc : Nat.card J = Nat.card (projSU 4 2 1) * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup p.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective p hp).toEquiv, hker, hZ]
  exact ⟨MulEquiv.ofBijective α (hα.bijective_of_nat_card_le (by rw [hc₀, hc]))⟩

theorem noRankThreeDoubleCover_psu42 :
    NoRankThreeDoubleCover (projSU 4 2 1) := by
  intro J _ _ hq hZ ⟨e⟩
  obtain ⟨α⟩ := nonempty_mulEquiv_statedSp_of_double_cover hq.1 hZ e
  have h2 := pRank_le_two_of_mulEquiv α
  omega

end DoubleCoverRanksTwo

end CFSG.RankThree.PartTwo.Sec4.Census
