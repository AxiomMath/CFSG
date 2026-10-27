module

public import CFSG.RankThree.PartTwo.Sec8.Hering611Defs
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint

section Facts

@[expose] def KF611InspectField : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E T : Subgroup G) (d : G)
    (S K : Subgroup G), Cfg611 G A c L E T d S K →
    (∃ x ∈ A, KFacts.InducesStdKind K x .field ∨ KFacts.InducesStdKind K x .graphField) →
    (∃ n : ℕ, 1 ≤ n ∧
      Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 2 (GaloisField 3 (3 * n)))) ∨
      (Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSp 2 (GaloisField 2 3)) ∧
        KFacts.InducesStdKind K c .field)

@[expose] def KF611InspectU4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E T : Subgroup G) (d : G)
    (S K : Subgroup G), Cfg611 G A c L E T d S K →
    (∃ n : ℕ, Odd n ∧ Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSU 4 2 n)) → False

@[expose] def KF611Invol : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E T : Subgroup G) (d : G)
    (S K : Subgroup G), Cfg611 G A c L E T d S K →
    (StatedClassicalModel (K ⧸ aschbacherSolvableCore 3 K) .PSp 3 2 1 ∨
      (Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* alternatingGroup (Fin 9)) ∧ c ∈ K) ∨
      (Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSp 2 (GaloisField 2 3)) ∧
        KFacts.InducesStdKind K c .field)) →
    ∃ t : G, t ^ 2 = 1 ∧ KFacts.InducesKindPSL2 (GaloisField 3 (3 * 2)) L t .field

@[expose] def KF611J3CoverFuse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E T : Subgroup G) (d : G)
    (S K : Subgroup G), Cfg611 G A c L E T d S K →
    Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) NativeSporadic.J3 →
    ∃ a ∈ A, a ∈ L ∧ a ≠ 1 ∧ IsConj a d

@[expose] def KF611J3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E T : Subgroup G) (d : G)
    (S K : Subgroup G), Cfg611 G A c L E T d S K →
    Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* NativeSporadic.J3) →
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set G)

end Facts

end CFSG.RankThree.PartTwo.Sec8.Hering611
