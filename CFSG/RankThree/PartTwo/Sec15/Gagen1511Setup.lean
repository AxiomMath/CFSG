module

public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.RankThree.PartTwo.Sec13.Steps
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec13.Item131a
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.Assembly.Defs
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate3139
import CFSG.RankThree.PartOne.Q1327T.ThetaLift
import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaRankThree
import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec16.Item1611Facts131
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofLThree
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Q1327T.Defs
import CFSG.RankThree.PartOne.S12.Equivariance
import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import Certificates.Certificate8166
import Certificates.Certificate8169

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1511Point

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem facts_of_prod_of_isoLThreePi {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) :
    Nat.card (A ⊓ L : Subgroup G) = 9 ∧ c ∉ L ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hD := h.toSec13Data
  haveI : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt).1
  obtain ⟨-, hq2⟩ := Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi he hiso
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
    obtain ⟨π, K, _, hKf, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
    have h2 : 2 < p ^ e := by
      have hp2 : 2 ≤ p ^ e :=
        (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
      omega
    exact Sec13.center_eq_bot_of_mulEquiv φ (Sec13.center_projImage_slPi hKf hq h2)
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot hD hZ
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    Sec13.card_inf_eq_nine hD (Sec13.isPerfect_lBar hD) hprod.some
  exact ⟨h9, hcL, Sec13.eq_sup_of_card_nine hD h9 fun hc => hcL hc.2⟩

private theorem isElemAbelian_inf {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) :
    CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
  ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩,
    fun x hx => hD.isElemAbelian.2 x hx.1⟩

private theorem isElemAbelian_image_inf {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L) :
    CFSG.Assembly.IsElemAbelian 3
      (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) := by
  rw [Subgroup.inf_subgroupOf_right]
  exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) (A.subgroupOf L)
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 A L hD.isElemAbelian)

private theorem card_image_inf {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    Nat.card (((A ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 9 := by
  have hP3 : IsPGroup 3 ((A ⊓ L).subgroupOf L) := fun x => by
    have hx3 : ((x : L) : G) ^ 3 = 1 :=
      hD.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp x.2).1
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using hx3))⟩
  rw [CFSG.RankThree.PartOne.Q1327T.card_map_mk_of_isPGroup Nat.prime_three hP3,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]

private theorem exists_mem_inf_of_mem_image {A L : Subgroup G}
    {z : ↥L ⧸ aschbacherSolvableCore 3 ↥L}
    (hz : z ∈ ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)))
    (hz1 : z ≠ 1) :
    ∃ y ∈ A ⊓ L, y ≠ 1 ∧ ∃ hyL : y ∈ L,
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ⟨y, hyL⟩ = z := by
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hz
  refine ⟨y', Subgroup.mem_subgroupOf.mp hy', fun hy1 => hz1 ?_, y'.2, rfl⟩
  have : y' = 1 := Subtype.ext hy1
  rw [this, map_one]

private theorem normalizer_image_transitive {A L : Subgroup G} {c : G}
    (hc3 : c ^ 3 = 1) (hcL : c ∉ L) (hLc : ∀ l ∈ L, l * c = c * l)
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hB : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hQ : Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
      Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) :
    ∀ y₀ ∈ ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
      y₀ ≠ 1 →
      ∀ y₁ ∈ ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
        y₁ ≠ 1 →
        ∃ w ∈ Subgroup.normalizer
            ((((A ⊓ L).subgroupOf L).map
              (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :
                Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
              Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)),
          w * y₀ * w⁻¹ = y₁ := by
  intro z₀ hz₀ hz₀1 z₁ hz₁ hz₁1
  obtain ⟨y₀, hy₀, hy₀1, hy₀L, rfl⟩ := exists_mem_inf_of_mem_image hz₀ hz₀1
  obtain ⟨y₁, hy₁, hy₁1, hy₁L, rfl⟩ := exists_mem_inf_of_mem_image hz₁ hz₁1
  obtain ⟨w, hwL, hwN, hw⟩ :=
    exists_conj_eq_of_autIn hc3 hcL hLc hAc hB h9 hQ hy₀ hy₁ hy₀1 hy₁1
  refine ⟨(QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ⟨w, hwL⟩, ?_, ?_⟩
  · have hwN' : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.normalizer
        (((A ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp hwN (x : G)
    exact Subgroup.le_normalizer_map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
      ⟨_, hwN', rfl⟩
  · rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    exact Subtype.ext hw

theorem hessian_of_prod
    (h131a : Item131a) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) :
    CFSG.Assembly.IsElemAbelian 3
        (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) ∧
      Nat.card (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 9 ∧
      ∀ y₀ ∈ ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
        y₀ ≠ 1 →
        ∀ y₁ ∈ ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
          y₁ ≠ 1 →
          ∃ w ∈ Subgroup.normalizer
              ((((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :
                Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)),
            w * y₀ * w⁻¹ = y₁ := by
  have hD := h.toSec13Data
  obtain ⟨h9, hcL, hAc⟩ := facts_of_prod_of_isoLThreePi h he hiso hprod
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hD.mem_A
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  have hB := isElemAbelian_inf hD
  have hQ := Sec16.Proof1611Res.facts131_odd h131a hD hcL
    ⟨p, e, inferInstance, he, hiso⟩ hprod
  exact ⟨isElemAbelian_image_inf hD, card_image_inf hD h9,
    normalizer_image_transitive hc3 hcL hLc hAc hB h9 hQ⟩

end CFSG.RankThree.PartTwo.Sec15.Proof1511Point
