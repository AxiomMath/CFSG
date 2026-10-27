module

public import CFSG.RankThree.PartTwo.Sec8.Item812Proof89
public import CFSG.RankThree.PartTwo.Sec13.Item138N
public import CFSG.RankThree.PartTwo.Sec4.Statements417
public import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofTools
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofXNormal
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofTools
import CFSG.RankThree.PartTwo.KFacts.KS44Transport
import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.Classical.EvenSurvivingScalarRank
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.RankThree.PartTwo.KFacts.K71Lift
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import CFSG.Foundations
public import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item812Res4

section Image

variable {K : Type} [Group K] [Finite K]

theorem core_map_mk'_eq_bot {Y₀ : Subgroup K} (hY₀ : Y₀ ∈ thetaComponents 3 K) :
    aschbacherSolvableCore 3 ↥(Y₀.map (QuotientGroup.mk' (aschbacherSolvableCore 3 K))) = ⊥ := by
  obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map Nat.prime_three hY₀.2.1
  obtain ⟨hs, -, hp, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Y₀) Nat.prime_three
  have h1 := (solvable_prime_complement_core_quotient_centralizers Nat.prime_three
    (aschbacherSolvableCore 3 ↥Y₀) hs hp).2.2.1
  have h2 := aschbacherSolvableCore_map_mulEquiv Nat.prime_three η
  rw [← h2, h1, Subgroup.map_bot]

theorem subgroupMap_mem_core_iff {Y₀ : Subgroup K} (hY₀ : Y₀ ∈ thetaComponents 3 K) (l : Y₀) :
    (QuotientGroup.mk' (aschbacherSolvableCore 3 K)).subgroupMap Y₀ l ∈
        aschbacherSolvableCore 3 ↥(Y₀.map (QuotientGroup.mk' (aschbacherSolvableCore 3 K))) ↔
      l ∈ aschbacherSolvableCore 3 ↥Y₀ := by
  rw [core_map_mk'_eq_bot hY₀, Subgroup.mem_bot]
  have hint := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hY₀.2.1
  constructor
  · intro h1
    have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (l : K) = 1 :=
      congrArg Subtype.val h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h4 : (l : K) ∈ inSubgroup (aschbacherSolvableCore 3) Y₀ := by
      rw [hint]
      exact ⟨l.2, h2⟩
    obtain ⟨l', hl', hl'e⟩ := h4
    have : l' = l := Subtype.ext hl'e
    rwa [← this]
  · intro h1
    apply Subtype.ext
    have h3 : (l : K) ∈ Y₀ ⊓ aschbacherSolvableCore 3 K := by
      rw [← hint]
      exact ⟨l, h1, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr h3.2

end Image

end Item812Res4

section Final

open Item812Res4
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Blueprint

@[expose] def KF89JRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ p : ℕ, p.Prime → 3 < p →
      CFSG.Assembly.RankThreeEven.localRank p
        (↥(Subgroup.centralizer ({a} : Set G)) ⧸
          aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))) < 3

@[expose] def KF89JCentA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y₀ ∈ thetaComponents 3 ↥(Subgroup.centralizer ({a} : Set G)),
      sec8I L a ⊔ sec8J X a ≤ Y₀.map (Subgroup.centralizer ({a} : Set G)).subtype →
      ∀ x : ↥(Subgroup.centralizer ({a} : Set G)), (x : G) ∈ A →
        (∀ y ∈ Y₀, x * y * x⁻¹ * y⁻¹ ∈
          aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))) →
        (x : G) ∈ Subgroup.zpowers a

@[expose] def KF89JComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y₀ ∈ thetaComponents 3 ↥(Subgroup.centralizer ({a} : Set G)),
      sec8I L a ⊔ sec8J X a ≤ Y₀.map (Subgroup.centralizer ({a} : Set G)).subtype →
      ∀ hb : b ∈ Subgroup.centralizer ({a} : Set G),
        IsComponent ((((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
            (QuotientGroup.mk'
              (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))))).subgroupOf
          (Y₀.map (QuotientGroup.mk'
              (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))) ⊓
            Subgroup.centralizer ({(QuotientGroup.mk'
              (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))) ⟨b, hb⟩)} :
                Set (↥(Subgroup.centralizer ({a} : Set G)) ⧸
                  aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))))) ∧
        ((∃ m : ℕ, ChevalleyExceptionalModel
            ↥(((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))))) .G2 2 m) ∨
          Nonempty (((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))) ≃*
            projSU 3 3 1) ∨
          (∃ m : ℕ, ReeTitsModel
            ↥(((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))))) .twistedF4
                  2 m) ∨
          ReeTitsModel
            ↥(((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))))) .Tits 2 1 ∨
          (∃ m : ℕ, 2 ≤ m ∧ Nonempty
            (((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))) ≃*
              projSp 2 (GaloisField 2 m))) ∨
          Nonempty (((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))) ≃*
            alternatingGroup (Fin 6)) ∨
          (∃ m : ℕ, Odd m ∧ Nonempty
            (((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))) ≃*
              projSU 3 2 m))) ∧
        (Nonempty (((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))) ≃*
            alternatingGroup (Fin 6)) →
          Nonempty (perfectResidual (barCentralizer (Subgroup.zpowers a) X) ≃*
            alternatingGroup (Fin 6)))

end Final

end CFSG.RankThree.PartTwo.Sec8
