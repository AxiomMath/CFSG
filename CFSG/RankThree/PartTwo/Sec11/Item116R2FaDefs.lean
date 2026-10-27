module

public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace CFSG.RankThree.PartTwo.Sec11

@[expose] def ThreeCoverModelA' (Q : Type) [Group Q] : Prop :=
  (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ (p = 2 ∨ e ≤ 2) ∧ Sec4.IsoLThreePi Q p e) ∨
    Nonempty (Q ≃* alternatingGroup (Fin 6)) ∨ Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (Q ≃* Blueprint.NativeSporadic.M22) ∨ Nonempty (Q ≃* Blueprint.NativeSporadic.ON)

@[expose] def ThreeCentralCoverOmegaNonabelian' : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → IsPGroup 3 (Subgroup.center J) →
    Subgroup.center J ≠ ⊥ → ThreeCoverModelA' (J ⧸ Subgroup.center J) →
      ∀ S : Sylow 3 J, ∃ x ∈ (S : Subgroup J), ∃ y ∈ (S : Subgroup J),
        x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x

end CFSG.RankThree.PartTwo.Sec11
