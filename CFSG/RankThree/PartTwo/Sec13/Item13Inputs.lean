module

public import CFSG.RankThree.PartTwo.Sec13.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item13SetupAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → partTwoS G = ∅ →
    ∀ A ∈ partTwoF G, A ∉ partTwoT G →
      ∀ c : G, Subgroup.zpowers c ∈ omegaA A → ∃ L : Subgroup G, L ∈ lA A c

@[expose] def K410NotInverted : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    L ∈ thetaComponentsAt 3 c → CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 27 → c ∈ A →
    c ≠ 1 → A ≤ Subgroup.normalizer (L : Set G) →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) →
    Sec8.IsZ3PGLThreePi (lBarA c L A) → (∃ x ∈ A, Sec4.InducesTypeOn L x 3) →
    ∀ d a t : G, A ⊓ L = Subgroup.zpowers d → d ≠ 1 → a ∈ A →
      a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d →
      t ∈ Subgroup.normalizer (L : Set G) → t ∈ Subgroup.normalizer (A : Set G) →
      t * a * t⁻¹ = a → t * d * t⁻¹ = d⁻¹ → False

@[expose] def NotSLTwoOfHypT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypT A → ¬ Sec4.IsSLThreePiTwo (lBarA c L A)

@[expose] def SporadicModels131 : Prop :=
  (Group.IsPerfect CFSG.Blueprint.NativeSporadic.M22 ∧
    Subgroup.center CFSG.Blueprint.NativeSporadic.M22 = ⊥) ∧
  (Group.IsPerfect CFSG.Blueprint.NativeSporadic.M12 ∧
    Subgroup.center CFSG.Blueprint.NativeSporadic.M12 = ⊥) ∧
  (Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 ∧
    Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥)

@[expose] def SLTwoCenter : Prop :=
  ∀ (X : Type) [Group X], Sec4.IsSLThreePiTwo X → ∀ Q : Subgroup X, Q.Normal →
    Group.IsPerfect Q → Q ≠ ⊥ → Subgroup.center X ≤ Q

end CFSG.RankThree.PartTwo.Sec13
