module

public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1518
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import Certificates.Certificate10019
public import Certificates.Certificate3139
public import Certificates.Certificate8166
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.RankThree.PartTwo.Sec19.Step1913
import CFSG.RankThree.PartTwo.KFacts.KS18MultProof
import CFSG.RankThree.PartTwo.Sec14.Item1411
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.RankThree.PartTwo.Sec13.Item135
import CFSG.Certificates.WordSubgroupRel
import CFSG.LieType.Multipliers.ProductKernel
import CFSG.LieType.Multipliers.U42Bridge
import CFSG.LieType.Multipliers.U43Action
import CFSG.LieType.Multipliers.U43BridgeInputs
import CFSG.LieType.Multipliers.U62Action
import CFSG.LieType.Multipliers.U62Bridge
import CFSG.LieType.Multipliers.U62Kernel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
import CFSG.Monster.B.Classical.PlaneAut
import CFSG.Monster.B.TwoA.Amalgam.Data
import CFSG.Monster.B.TwoA.Sp8.Par1
import CFSG.Monster.B.TwoA.Unitary.LinThree
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.RankThree.PartTwo.Sec19.Item1912
import CFSG.RankThree.PartTwo.Sec21.Item22Statements
import CFSG.Sporadic.Presentation.Common
import CFSG.Sporadic.SmallOddCore.CheckSpec
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
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
import Certificates.Certificate3951
import Certificates.Certificate8033
import Certificates.Certificate9130

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof1517

variable {G : Type} [Group G] [Finite G]

theorem normalizer_mem_scriptY2 {A T : Subgroup G} (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    Subgroup.normalizer (T : Set G) ∈ scriptY2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨normalizer_ne_top_of_isPGroup hsimp hnab hT hT2,
    hAT.trans Subgroup.le_normalizer⟩, fun h0 => ?_⟩
  have hPO : T ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (T : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hT2
  rw [h0] at hPO
  exact hT (le_bot_iff.mp hPO)

theorem eq_bot_of_noY2 {A L T : Subgroup G} (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hno : ∀ X ∈ scriptY2 A, ¬ L ≤ X) (hT2 : IsPGroup 2 T)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hLT : L ≤ Subgroup.normalizer (T : Set G)) :
    T = ⊥ := by
  by_contra hT
  exact hno _ (normalizer_mem_scriptY2 hsimp hnab hT hT2 hAT) hLT

theorem theta_eq_pCore_two
    (h135 : Item135Simple) {A : Subgroup G} {c : G}
    {L Y : Subgroup G} (h : Sec15R G A c L) (hctx : Ctx1514 A (lB A) c L Y) :
    aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L := by
  obtain ⟨p, e, hp, he, hiso, -⟩ := hctx.concl1515
  have hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := ⟨p, e, hp, he, hiso⟩
  exact Sec19.theta_eq_pCore_two_of_mult KFacts.KS14.ks18Mult
    (h135 G A c L h.toSec13Data (Or.inl hL3)) (Or.inl hL3)

theorem pCore_two_eq_bot {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hno : ∀ X ∈ scriptY2 A, ¬ L ≤ X) : CFSG.pCore 2 ↥L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 : CFSG.Open.pCoreOf 2 L = ⊥ :=
    eq_bot_of_noY2 h.isSimpleGroup h.nonabelian hno
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L)
      (h.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h0

theorem isSimpleGroup_of_noY2
    (h135 : Item135Simple) {A : Subgroup G} {c : G}
    {L Y : Subgroup G} (h : Sec15R G A c L) (hctx : Ctx1514 A (lB A) c L Y)
    (hno : ∀ X ∈ scriptY2 A, ¬ L ≤ X) : IsSimpleGroup ↥L := by
  obtain ⟨p, e, hp, he, hiso, -⟩ := hctx.concl1515
  have hθ : aschbacherSolvableCore 3 ↥L = ⊥ := by
    rw [theta_eq_pCore_two h135 h hctx]
    exact pCore_two_eq_bot h hno
  have := Proof1514.isSimpleGroup_of_isoLThreePi h.mem_thetaComponentsAt he hiso
  exact ((QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

omit [Finite G] in
theorem center_eq_bot_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : Group.IsPerfect X) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ x y : X, x * y = y * x := fun x y =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)
    have hbot : commutator X = ⊥ := by
      rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [commutatorElement_def, hcomm x y, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
    have htop : commutator X = ⊤ := hX.commutator_eq_top
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    have ha : a = 1 := by
      have : a ∈ commutator X := htop ▸ Subgroup.mem_top a
      rwa [hbot, Subgroup.mem_bot] at this
    have hb : b = 1 := by
      have : b ∈ commutator X := htop ▸ Subgroup.mem_top b
      rwa [hbot, Subgroup.mem_bot] at this
    exact hab (ha.trans hb.symm)

theorem center_eq_bot {A : Subgroup G} {c : G} {L Y : Subgroup G} (h : Sec15R G A c L)
    (hctx : Ctx1514 A (lB A) c L Y) :
    Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
  obtain ⟨p, e, hp, he, hiso, -⟩ := hctx.concl1515
  have := Proof1514.isSimpleGroup_of_isoLThreePi h.mem_thetaComponentsAt he hiso
  exact center_eq_bot_of_isSimpleGroup
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt).1

theorem point_facts {A : Subgroup G} {c : G} {L Y : Subgroup G} (h : Sec15R G A c L)
    (hctx : Ctx1514 A (lB A) c L Y) :
    c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  obtain ⟨-, -, -, -, -, ⟨φ⟩, -⟩ := hctx.concl1515
  have hcL : c ∉ L := not_mem_of_center_eq_bot h.toSec13Data (center_eq_bot h hctx)
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    card_inf_eq_nine h.toSec13Data (isPerfect_lBar h.toSec13Data) φ
  exact ⟨hcL, h9, eq_sup_of_card_nine h.toSec13Data h9 fun hc => hcL hc.2⟩

theorem le_centralizer_inf {A : Subgroup G} {c : G} {L Y : Subgroup G} (h : Sec15R G A c L)
    (hctx : Ctx1514 A (lB A) c L Y) :
    A ≤ Subgroup.centralizer ((Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  obtain ⟨-, -, hAeq⟩ := point_facts h hctx
  rw [hAeq]
  refine sup_le ?_ (inf_le_right.trans ?_)
  · refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).1
  · intro l hl
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 l hl).symm

theorem odd_card_inf_centralizer {A : Subgroup G} {c : G} {L Y : Subgroup G}
    (h : Sec15R G A c L) (hctx : Ctx1514 A (lB A) c L Y) (hno : ∀ X ∈ scriptY2 A, ¬ L ≤ X) :
    Odd (Nat.card ↥(Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer (L : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X₀ := Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer (L : Set G) with hX₀
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set T := Subgroup.zpowers (t : G) with hT
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by
    rw [hT, Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one])
  have hCT : Subgroup.centralizer (X₀ : Set G) ≤ Subgroup.normalizer (T : Set G) := by
    intro g hg
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (Subgroup.mem_centralizer_iff.mp hg (t : G) t.2) k).eq
  have hLC : L ≤ Subgroup.centralizer (X₀ : Set G) := fun l hl =>
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 l hl).symm
  have hT0 := eq_bot_of_noY2 h.isSimpleGroup h.nonabelian hno hT2
    ((le_centralizer_inf h hctx).trans hCT) (hLC.trans hCT)
  have ht1 : (t : G) = 1 := by
    have : (t : G) ∈ T := Subgroup.mem_zpowers _
    rwa [hT0, Subgroup.mem_bot] at this
  have : orderOf t = 1 := by
    rw [orderOf_eq_one_iff]
    exact Subtype.ext ht1
  omega

end Proof1517

end CFSG.RankThree.PartTwo.Sec15
