module

public import CFSG.RankThree.PartTwo.Sec12.Item128Bar
public import CFSG.RankThree.PartTwo.Sec13.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lBarA)

@[expose] def KS128SLAInL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L → A ∈ partTwoE G →
    Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ a : G, Subgroup.zpowers a ∈ omegaA A → a ∉ Sec4.thetaQuotCentralizer L →
    ∀ K ∈ lA422 A a, c ∈ K →
      ((Sec8.IsZ3PGLThreePi (lBarA a K A) ∧
          Nonempty (Sec4.autIn K A ≃* Multiplicative (ZMod 3)) ∧
          ∃ x ∈ A, x ≠ 1 ∧ Sec4.InducesTypeOn K x 3) ∨
        (Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∧
          Nonempty (Sec4.autIn K A ≃* Equiv.Perm (Fin 3)))) →
      a ∈ L

@[expose] def KS128TypeCMove : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Sec4.IsSLThreePi X →
    ∀ x : X, x ∉ Subgroup.center X → x ^ 3 = 1 →
    ∀ Y : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 Y → Nat.card Y = 9 →
      MulAut.conj x ∈ Y → (∀ σ ∈ Y, σ x = x) →
      ∃ u : X, u * x * u⁻¹ * x⁻¹ ∈ Subgroup.center X ∧ u * x * u⁻¹ ≠ x ∧
        (∀ σ ∈ Y, σ u * u⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.center X) ∧
        ∀ σ ∈ Y, σ ∉ Subgroup.zpowers (MulAut.conj x) → σ u * u⁻¹ ∉ Subgroup.center X

end CFSG.RankThree.PartTwo.Sec12
