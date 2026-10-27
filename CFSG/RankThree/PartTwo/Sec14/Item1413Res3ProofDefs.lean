module

public import CFSG.RankThree.PartTwo.Sec13.Steps
public import CFSG.RankThree.PartTwo.Sec14.Item1411Chain
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

@[expose] noncomputable def Item1419OneR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        (Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7)) ∨
          IsLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') ∨
          Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M12)) →
        ∀ R ∈ scriptQPiStar A (lB A) L' (piOf 2),
          IsHyperplane A (A ⊓ Subgroup.centralizer (R : Set G))

@[expose] noncomputable def Item1419TwoR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        (Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7)) ∨
          IsLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') ∨
          Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M12)) →
        ∀ R ∈ scriptQPiStar A (lB A) L' (piOf 2),
          {F | F ∈ gammaA A (lB A) ∧ F ≤ A ⊓ Subgroup.centralizer (R : Set G)} =
            {Subgroup.zpowers c', A ⊓ Subgroup.centralizer (R : Set G) ⊓ L'}

@[expose] noncomputable def Step1419OneL3R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        IsLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') →
        ¬ Sec8.IsZ3PGLThreePi (lBarA c' L' A) →
        ∀ R ∈ scriptQPiStar A (lB A) L' (piOf 2),
          IsHyperplane A (A ⊓ Subgroup.centralizer (R : Set G))

@[expose] noncomputable def Step1419InvR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        (Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7)) ∨
          IsLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') ∨
          Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M12)) →
        ¬ Sec8.IsZ3PGLThreePi (lBarA c' L' A) →
        ∀ R ∈ scriptQPiStar A (lB A) L' (piOf 2),
          ∃ t ∈ L' ⊓ Subgroup.normalizer (A : Set G),
            ∀ x ∈ A ⊓ Subgroup.centralizer (R : Set G) ⊓ L', t * x * t⁻¹ = x⁻¹

@[expose] def KS1422M22Cent : Prop :=
  ∀ d : ↥CFSG.Blueprint.NativeSporadic.M22, orderOf d = 3 →
    ∃ V : Subgroup ↥CFSG.Blueprint.NativeSporadic.M22, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      V ≤ Subgroup.centralizer ({d} : Set ↥CFSG.Blueprint.NativeSporadic.M22) ∧
      Subgroup.centralizer ({d} : Set ↥CFSG.Blueprint.NativeSporadic.M22) ≤
        Subgroup.normalizer (V : Set ↥CFSG.Blueprint.NativeSporadic.M22)

@[expose] noncomputable def Step1418UniqR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ∀ B : Subgroup G, IsHyperplane A B →
        S ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ →
        ∀ b ∈ B, Subgroup.zpowers b ∈ gammaA A (lB A) →
          (∀ F ∈ gammaA A (lB A), F ≤ B → F = Subgroup.zpowers b) →
            ¬ ∀ T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ¬ IsConjIn (xA A) S T →
              T ≤ Subgroup.centralizer ({b} : Set G)

end CFSG.RankThree.PartTwo.Sec14
