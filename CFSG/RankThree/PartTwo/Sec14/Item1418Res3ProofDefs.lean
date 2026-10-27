module

public import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofCS
public import CFSG.RankThree.PartTwo.Sec14.Item1411Chain
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open Proof1418Res3 (ActsTrivOnLayer3)

@[expose] noncomputable def Step1418OffLayerR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ∀ B : Subgroup G, IsHyperplane A B →
        S ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ →
        ∀ b ∈ B, Subgroup.zpowers b ∈ gammaA A (lB A) →
          (∀ F ∈ gammaA A (lB A), F ≤ B → F = Subgroup.zpowers b) →
          (∀ T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), T ≤ Subgroup.centralizer ({b} : Set G)) →
          Subgroup.normalizer (A : Set G) ≤
            Subgroup.normalizer (Subgroup.zpowers b : Set G) →
          (∀ Lb ∈ lA A b, 3 ∣ Nat.card Lb → Subgroup.normalizer (A : Set G) ≤
            Subgroup.normalizer ((A ⊓ Lb : Subgroup G) : Set G)) →
            ∀ E : Subgroup G, IsHyperplane A E → (∀ F ∈ omegaA A, ¬ F ≤ E) →
              ∀ R : Subgroup G, R ≤ Subgroup.centralizer (E : Set G) → IsPGroup 2 R →
                A ≤ Subgroup.normalizer (R : Set G) → ⁅R, Subgroup.zpowers b⁆ = R →
                  ActsTrivOnLayer3 (Subgroup.centralizer (E : Set G)) R

@[expose] noncomputable def Step1422IQBLayerR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22) →
          Subgroup.normalizer (A : Set G) ≤
            Subgroup.normalizer ((A ⊓ L' : Subgroup G) : Set G) →
          (∀ d ∈ A ⊓ L', ∃ w ∈ Subgroup.normalizer (A : Set G),
            w * d = d * w ∧ w * c' * w⁻¹ = c' * d) →
          ∀ U : Subgroup G, U ≤ Subgroup.centralizer ((A ⊓ L' : Subgroup G) : Set G) →
            IsPGroup 2 U → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
              ActsTrivOnLayer3 (Subgroup.centralizer ((A ⊓ L' : Subgroup G) : Set G)) U

end CFSG.RankThree.PartTwo.Sec14
