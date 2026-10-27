module

public import CFSG.RankThree.PartTwo.Sec21.Item218Proof

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def IsCentral218 {G : Type*} [Group G] (L : Subgroup G) (d : G) : Prop :=
  ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧ d ∈ (Subgroup.center S).map S.subtype

@[expose] def iOf218 {G : Type} [Group G] (L : Subgroup G) (d : G) : Subgroup G :=
  inSubgroup CFSG.layer (L ⊓ Subgroup.centralizer ({d} : Set G))

@[expose] def Item2113Choice : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L →
      ∃ d ∈ A, d ≠ 1 ∧ IsCentral218 L d ∧ ∃ t ∈ starOf A L, IsTransvectionOn t ∧
        (commOf t).map A.subtype = Subgroup.zpowers d

@[expose] def Item219 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      d ∈ iOf218 L d ∧
      ((Nonempty (L ≃* NativeSporadic.He) ∧
          Sec4.IsTripleCover (iOf218 L d) (alternatingGroup (Fin 7))) ∨
        ((Nonempty (lBar L ≃* NativeSporadic.M24) ∨ Nonempty (lBar L ≃* NativeSporadic.J2) ∨
            Nonempty (lBar L ≃* NativeSporadic.Ru)) ∧
          Sec4.IsTripleCover (lBar (iOf218 L d)) (alternatingGroup (Fin 6))) ∨
        (Nonempty (L ≃* NativeSporadic.J4) ∧
          Nat.card (Subgroup.center (iOf218 L d)) = 6 ∧
          Nonempty (iOf218 L d ⧸ Subgroup.center (iOf218 L d) ≃* NativeSporadic.M22)) ∨
        (∃ n : ℕ, 0 < n ∧ Even n ∧
          (ChevalleyExceptionalModel (lBar L) .G2 2 n ∨
            ChevalleyExceptionalModel (lBar L) .trialityD4 2 n) ∧
          Nonempty (lBar (iOf218 L d) ≃* SL3 n)))

@[expose] def Item2110One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      Subgroup.centralizer ({d} : Set G) ≤
        Subgroup.normalizer ((iOf218 L d ⊔
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G)) :
            Subgroup G) : Set G)

@[expose] def Item2110Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      CFSG.GH74.GLS.oPrimeResidualOf 3
          (Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({d} : Set G)) ≤
        Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)

@[expose] def Item2110Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      ∃! J : Subgroup G, J ∈ thetaComponentsAt 3 d ∧ d ∈ J

@[expose] def Item2111 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ¬ IsIrreducibleOn (wStar A)

@[expose] def Item2112Unique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      ∀ Y : Subgroup G, Y ≤ Subgroup.closure ({c, d} : Set G) → Nat.card Y = 3 →
        (Subgroup.normalizer (Subgroup.closure ({c, d} : Set G) : Set G) ⊓
            Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) ≤
            Subgroup.normalizer (Y : Set G) ↔
          Y = Subgroup.zpowers c ∨ Y = Subgroup.zpowers d)

@[expose] def Item2112ND : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      Subgroup.normalizer (Subgroup.closure ({c, d} : Set G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)

end CFSG.RankThree.PartTwo.Sec21
