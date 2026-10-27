module

public import CFSG.RankThree.PartTwo.Sec12.Item128Bar
public import CFSG.RankThree.PartTwo.Sec13.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lBarA)
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Item125BarTC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L →
    (Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) →
    ∀ E : Subgroup G, Late.IsE27 E → E ≤ lcBar c L → c ∈ E →
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)

@[expose] def Item125Diag : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L →
    (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) →
    ∀ E : Subgroup G, Late.IsE27 E → E ≤ lcBar c L → c ∈ E →
      Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 →
      Nat.card (E ⊓ L : Subgroup G) = 3 →
      (∀ e ∈ E, ∃ l ∈ L, ∃ z ∈ Sec4.thetaQuotCentralizer L,
        e = l * z ∧ l ^ 3 = 1 ∧ l * z = z * l) →
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)

@[expose] def KS128NotHJTC : Prop :=
  Item125BarTC →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L → A ∈ partTwoE G →
    (Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) →
    ∀ a : G, Subgroup.zpowers a ∈ omegaA A → a ∉ Sec4.thetaQuotCentralizer L →
    ∀ K ∈ lA422 A a, c ∈ K →
      ¬ (Sec8.IsZ3PGLThreePi (lBarA a K A) ∧
          Nonempty (Sec4.autIn K A ≃* Multiplicative (ZMod 3)) ∧
          ∃ x ∈ A, x ≠ 1 ∧ Sec4.InducesTypeOn K x 3) ∧
      ¬ (Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∧
          Nonempty (Sec4.autIn K A ≃* Equiv.Perm (Fin 3)))

end CFSG.RankThree.PartTwo.Sec12
