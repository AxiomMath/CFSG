module

public import CFSG.RankThree.PartTwo.Sec11.Item1117Res5ProofSymTypes

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Statements

@[expose] def Sym1119NotLThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sym1119Ctx G A c L a R Y d x s r g →
      ¬ ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi (L ⧸ aschbacherSolvableCore 3 L) 2 (3 * n)

@[expose] def Sym1119Numbers : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sym1119Ctx G A c L a R Y d x s r g →
      (¬ ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi (L ⧸ aschbacherSolvableCore 3 L) 2 (3 * n)) →
        orderOf x ≤ 27 ∧ orderOf r ≤ 9

@[expose] def Sym1119Item111 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sym1119Ctx G A c L a R Y d x s r g →
      ∀ e ∈ A, e ∉ Subgroup.closure ({c, d} : Set G) → (∃ k : G, k * c * k⁻¹ = e) →
        ¬ YNotField c L e

end Statements

end CFSG.RankThree.PartTwo.Sec11

end
