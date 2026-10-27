module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec6.Item611Res5ProofL43Cent
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def Item611E81V : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
        T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
      ((A ≤ L ∧ ∃ (K : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) (_ : K.Normal),
          K = ((Subgroup.zpowers c).subgroupOf L).map
            (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) ∧
          (Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸ K ≃* projSU 4 3 1) ∨
            Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸ K ≃* Blueprint.NativeSporadic.McL))) ∨
        (A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧ c ∉ L ∧
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.McL) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 4 (GaloisField 3 1)) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 3 1)))) →
      ∀ t ∈ L, t ∈ Subgroup.normalizer (A : Set G) → t ≠ 1 → t ^ 2 = 1 →
        A ⊓ Subgroup.centralizer {t} ∈ partTwoE G →
        ∃ V : Subgroup G, V ≤ Subgroup.centralizer {t} ∧
          Subgroup.centralizer {t} ≤ Subgroup.normalizer (V : Set G) ∧
          CFSG.Assembly.IsElemAbelian 2 V ∧ 4 ≤ Nat.card V

@[expose] def Item611E81Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
        T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
      ((A ≤ L ∧ ∃ (K : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) (_ : K.Normal),
          K = ((Subgroup.zpowers c).subgroupOf L).map
            (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) ∧
          (Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸ K ≃* projSU 4 3 1) ∨
            Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸ K ≃* Blueprint.NativeSporadic.McL))) ∨
        (A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧ c ∉ L ∧
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.McL) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 4 (GaloisField 3 1)) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 3 1)))) →
      ∀ t ∈ L, t ∈ Subgroup.normalizer (A : Set G) → t ≠ 1 → t ^ 2 = 1 →
        A ⊓ Subgroup.centralizer {t} ∈ partTwoE G →
      ∀ V : Subgroup G, V ≤ Subgroup.centralizer {t} →
        Subgroup.centralizer {t} ≤ Subgroup.normalizer (V : Set G) →
        CFSG.Assembly.IsElemAbelian 2 V → 4 ≤ Nat.card V →
      ∀ U ∈ fourGroupsMinus (A ⊓ Subgroup.centralizer {t}), U ≤ V →
      ∀ d ∈ A, d ≠ 1 → ∀ K ∈ lZeroStarAt A d, A ⊓ thetaQuotCentralizer K = Subgroup.zpowers d →
        K ∈ lZero (A ⊓ Subgroup.centralizer {t}) →
      ∀ R ∈ fourGroupsMinus (A ⊓ Subgroup.centralizer {t}), R ≤ K →
        R ⊓ inSubgroup (aschbacherSolvableCore 3) K = ⊥ →
        (A ⊓ Subgroup.centralizer {t}) ⊓ Subgroup.centralizer (R : Set G) =
          (A ⊓ Subgroup.centralizer {t}) ⊓ Subgroup.centralizer (U : Set G) → False

namespace Res611Res5

variable {G : Type} [Group G]

theorem mem_inf_centralizer_of_mem {A L : Subgroup G} {c t : G} (hcA : c ∈ A)
    (hL : L ∈ thetaComponentsAt 3 c) (htL : t ∈ L) : c ∈ A ⊓ Subgroup.centralizer {t} := by
  refine ⟨hcA, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  exact (Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_mem_thetaComponentsAt hL
    htL)).symm

theorem mem_thetaComponentFamily_inf {A L : Subgroup G} {c t : G} (hcA : c ∈ A) (hc1 : c ≠ 1)
    (hL : L ∈ thetaComponentsAt 3 c) (htL : t ∈ L) :
    L ∈ thetaComponentFamily 3 (A ⊓ Subgroup.centralizer {t}) :=
  mem_thetaComponentFamily_iff.mpr ⟨c, mem_inf_centralizer_of_mem hcA hL htL, hc1, hL⟩

end Res611Res5

open Res611Res5

end CFSG.RankThree.PartTwo.Sec6
