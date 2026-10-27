module

public import CFSG.RankThree.PartTwo.Sec12.Item128Bar
public import CFSG.RankThree.PartTwo.Sec12.Item128Bar125
public import CFSG.RankThree.PartTwo.Sec13.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lBarA)

@[expose] def KS128BCensus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L → A ∈ partTwoE G → A ∉ partTwoT G →
    (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) →
    ∀ b : G, Subgroup.zpowers b ∈ omegaA A → b ∈ Sec4.thetaQuotCentralizer L →
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∧
      ∀ K ∈ lA422 A b,
        Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.J2)

@[expose] def KS128NotHJ : Prop :=
  Item125Bar →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L → A ∈ partTwoE G →
    (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) →
    ∀ a : G, Subgroup.zpowers a ∈ omegaA A → a ∉ Sec4.thetaQuotCentralizer L →
    ∀ K ∈ lA422 A a, c ∈ K →
      ¬ (Sec8.IsZ3PGLThreePi (lBarA a K A) ∧
          Nonempty (Sec4.autIn K A ≃* Multiplicative (ZMod 3)) ∧
          ∃ x ∈ A, x ≠ 1 ∧ Sec4.InducesTypeOn K x 3) ∧
      ¬ (Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∧
          Nonempty (Sec4.autIn K A ≃* Equiv.Perm (Fin 3)))

@[expose] def Gap128OTwoHJ : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SectionFourHyp X → Group.IsPerfect X →
    Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    Nonempty (X ⧸ CFSG.pCore 2 X ≃* CFSG.Blueprint.NativeSporadic.J2)

end CFSG.RankThree.PartTwo.Sec12
