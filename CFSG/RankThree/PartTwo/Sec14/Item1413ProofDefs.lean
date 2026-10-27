module

public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec14.Item1411Chain
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

@[expose] noncomputable def Item1416R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ omegaA A → ∀ L' ∈ lA A c',
        IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2)

@[expose] noncomputable def Item1417_2R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2),
        ¬ IsConjIn (xA A) S T → ∀ a ∈ A, a ≠ 1 →
          S ⊓ Subgroup.centralizer {a} ≠ ⊥ → T ⊓ Subgroup.centralizer {a} ≠ ⊥ →
            Subgroup.zpowers a ∈ gammaA A (lB A)

@[expose] noncomputable def Item1418R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ∀ B : Subgroup G, IsHyperplane A B →
        S ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ →
          ∃ F₁ ∈ gammaA A (lB A), ∃ F₂ ∈ gammaA A (lB A), F₁ ≠ F₂ ∧ F₁ ≤ B ∧ F₂ ≤ B

@[expose] noncomputable def Item1419R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        (Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7)) ∨
          IsLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') ∨
          Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M12)) →
        ∀ R ∈ scriptQPiStar A (lB A) L' (piOf 2),
          IsHyperplane A (A ⊓ Subgroup.centralizer (R : Set G)) ∧
            {F | F ∈ gammaA A (lB A) ∧ F ≤ A ⊓ Subgroup.centralizer (R : Set G)} =
              {Subgroup.zpowers c', A ⊓ Subgroup.centralizer (R : Set G) ⊓ L'}

@[expose] noncomputable def Item1420R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
          Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22)

@[expose] noncomputable def Step1420NotL3R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        ¬ IsLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L')

@[expose] noncomputable def Step1420NotA7R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7))

@[expose] noncomputable def Step1421M12R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M12) →
          Nat.card ↥(A ⊓ L') = 9 ∧
          ∃ d ∈ A ⊓ L', d ≠ 1 ∧
            (∀ x ∈ A, x ∉ Subgroup.closure ({c', d} : Set G) →
              ∃ R ∈ scriptQPiStar A (lB A) L' (piOf 2),
                A ⊓ Subgroup.centralizer (R : Set G) = Subgroup.closure {c', x}) ∧
            ∀ R₁ ∈ scriptQPiStar A (lB A) L' (piOf 2), ∀ R₂ ∈ scriptQPiStar A (lB A) L' (piOf 2),
              A ⊓ Subgroup.centralizer (R₁ : Set G) = A ⊓ Subgroup.centralizer (R₂ : Set G) →
                R₁ = R₂

@[expose] noncomputable def Step1421M22R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ a : G, Subgroup.zpowers a ∈ gammaA A (lB A) → ∀ La ∈ lA A a,
        Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.M22) →
          omegaA A ⊆ orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers a)

@[expose] noncomputable def Step1422NotWHR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ a : G, Subgroup.zpowers a ∈ gammaA A (lB A) → ∀ La ∈ lA A a,
        Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.M22) →
          ¬ Subgroup.normalizer (A : Set G) ≤
            Subgroup.normalizer (Subgroup.zpowers a : Set G)

@[expose] noncomputable def Step1422TransvR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22) →
          ∀ d ∈ A ⊓ L', ∃ w ∈ Subgroup.normalizer (A : Set G),
            w * d = d * w ∧ w * c' * w⁻¹ = c' * d

@[expose] noncomputable def Step1422CentR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22) →
          ∃ R ∈ scriptQPiStar A (lB A) L' (piOf 2), ∃ d ∈ A ⊓ L', d ≠ 1 ∧
            CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c', d} : Set G)) ≠ ⊥ ∧
            CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c', d} : Set G)) ≤ R

@[expose] noncomputable def Step1422SR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22) →
          ∀ R ∈ scriptQPiStar A (lB A) L' (piOf 2),
            ∃ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), R ≤ S ∧
              Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
                Subgroup.normalizer (Subgroup.zpowers c' : Set G)

end CFSG.RankThree.PartTwo.Sec14
