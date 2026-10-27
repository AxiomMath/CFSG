module

public import CFSG.RankThree.PartTwo.Sec8.Notation
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def IsList82One (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 2 (GaloisField 3 3)) ∨
    (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧
      Nonempty (X ≃* projSL 2 (GaloisField p (3 * e)))) ∨
    ∃ m : ℕ, 1 ≤ m ∧
      (Nonempty (X ≃* projSL 2 (GaloisField 2 (3 * m))) ∨ IsoLThreeMinusPi X 2 (3 * m) ∨
        Sec4.IsSLThreePiAt X (2 ^ (3 * m)))

@[expose] def IsList82Two (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, Odd n ∧
    ((∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
        q.p = 2 ∧ q.exponent = n ∧
          Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∨
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 * n ∧ Sec4.IsoGTwo X q) ∨
      (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid), 2 * m + 1 = 3 * n ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group)) ∨
      Nonempty (X ≃* projSp 2 (GaloisField 2 (3 * n))) ∨
      Nonempty (X ≃* projSU 3 2 (3 * n)) ∨
      Sec4.IsSLThreePiAt X (2 ^ (3 * n)))

@[expose] def Item82 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G),
    Hyp81 G A c L a →
      (Nat.card A = 27 ∧ IsList82One (L ⧸ aschbacherSolvableCore 3 L)) ∨
        (Nat.card A = 81 ∧ IsList82Two (L ⧸ aschbacherSolvableCore 3 L))

@[expose] def Item82One :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G),
    Hyp81 G A c L a → Nat.card A = 27 → IsList82One (L ⧸ aschbacherSolvableCore 3 L)

theorem item82One_of_item82
    (h82 : Item82) : Item82One := by
  intro G _ _ A c L a h h27
  rcases h82 G A c L a h with ⟨-, h1⟩ | ⟨h81, -⟩
  · exact h1
  · exact absurd (h27.symm.trans h81) (by norm_num)

@[expose] def Item812 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G),
    Hyp81 G A c L a → Nat.card A = 27

end CFSG.RankThree.PartTwo.Sec8
