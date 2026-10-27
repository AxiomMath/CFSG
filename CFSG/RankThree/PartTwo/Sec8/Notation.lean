module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {G : Type*} [Group G]

@[expose] def IsoLThreeMinusPi (X : Type) [Group X] (p e : ℕ) [Fact p.Prime] : Prop :=
  (p ^ e % 3 = 1 ∧ Nonempty (X ≃* projSU 3 p e)) ∨
    (p ^ e % 3 = 2 ∧ Nonempty (X ≃* projSL 3 (GaloisField p e)))

@[expose] def InvTwoBarNontrivial [Finite G] (E L : Subgroup G) : Prop :=
  ∃ X : Subgroup (L ⧸ aschbacherSolvableCore 3 L), X ≠ ⊥ ∧ IsPGroup 2 X ∧
    ∀ τ ∈ Sec4.autThetaQuot E L, ∀ x ∈ X, τ x ∈ X

structure Hyp81 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a : G) : Prop extends PartTwoStanding G where
  mem_partTwoF : A ∈ partTwoF G
  mem_A : c ∈ A
  ne_one : c ≠ 1
  mem_thetaComponentsAt : L ∈ thetaComponentsAt 3 c
  sectionCentralizer_eq :
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G)
  a_mem : a ∈ A
  a_ne_one : a ≠ 1
  inducesStdKind :
    KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField
  exists_invariant_two : 27 < Nat.card A →
    ∃ E ∈ partTwoE G, E ≤ A ∧ ∃ U ∈ invariantPiSubgroups L E (piOf 2), U ≠ ⊥
  partTwoE_eq : Nat.card A = 27 → partTwoE G = partTwoF G

theorem Hyp81.a_mem_normalizer {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} (h : Hyp81 G A c L a) : a ∈ Subgroup.normalizer (L : Set G) := by
  rcases h.inducesStdKind with h' | h'
  · exact h'.mem_normalizer
  · exact h'.mem_normalizer

end CFSG.RankThree.PartTwo.Sec8
