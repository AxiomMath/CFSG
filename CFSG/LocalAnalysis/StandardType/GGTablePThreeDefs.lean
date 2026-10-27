module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Datum

@[expose] def GGTablePThreeDatum {X : Type} [Group X] (A : Subgroup (MulAut X)) (δ : MulAut X)
    (J : Subgroup X) : Prop :=
  GGKLocal A δ J ∧
    (∀ Q : Subgroup X, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J) ∧
    3 ^ 3 ≤ Nat.card A ∧
    LargeEvenMarking X (fun lab _ _ I _ θ => LargeEvenSplit 3 lab ∧ GGInducedInn A θ I)

end Datum

section Table

@[expose] def GGTablePThreeA2CentrelessKnown : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), GGTablePThreeDatum A δ J →
      LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab) → Subgroup.center J = ⊥ →
        GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
          (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
            (lab.tag = .A ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
            (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1)

@[expose] def GGTablePThreeTwA2ScalarKnown : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), GGTablePThreeDatum A δ J →
      LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA) →
      Subgroup.center J ≠ ⊥ →
        GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
          (lab.tag = .twA ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨
            (lab.tag = .twA ∧ lab.rank = 4 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ Nat.card A = 3 ^ 3) ∨
            (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1)

@[expose] def GGTablePThreeTriD4Known : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), GGTablePThreeDatum A δ J →
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .triD4) →
        GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
          (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)

@[expose] def GGTablePThreeD4OddKnown : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), GGTablePThreeDatum A δ J →
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n) →
        GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
          (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twD ∧ lab.rank = 5) ∨
            (lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) ∨ (lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1)

@[expose] def GGTablePThreeA1Known : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), GGTablePThreeDatum A δ J →
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1) →
        Nat.card A = 3 ^ 3 ∧
          GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
            (lab.tag = .A ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
              (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1)

end Table

section Parabolic

@[expose] def GGTablePThreeU6NoTwoGroupKnown : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), GGTablePThreeDatum A δ J →
      Nat.card A = 3 ^ 3 →
      LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) →
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1) →
        ¬ ∃ U : Subgroup (MulAut X), U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U

@[expose] def GGTablePThreeU5NoTwoGroupKnown : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), GGTablePThreeDatum A δ J →
      Nat.card A = 3 ^ 3 →
      LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 4 ∧ 3 ∣ 2 ^ lab.n + 1) →
      LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA) →
      Subgroup.center J ≠ ⊥ →
        ¬ ∃ U : Subgroup (MulAut X), U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U

end Parabolic

section Bundles

@[expose] def GGTablePThreeKnown : Prop :=
  (∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ → ∀ (A : Subgroup (MulAut X)) (δ : MulAut X)
      (J : Subgroup X), GGTablePThreeDatum A δ J → ¬ LargeEvenMarking J (fun lab _ _ _ _ _ =>
      GGLabelG2 lab)) ∧ GGTablePThreeA2CentrelessKnown ∧ GGTablePThreeTwA2ScalarKnown ∧
    GGTablePThreeTriD4Known ∧ GGTablePThreeD4OddKnown ∧ GGTablePThreeA1Known ∧
    GGTablePThreeU6NoTwoGroupKnown ∧ GGTablePThreeU5NoTwoGroupKnown

@[expose] def GGD4OddCentKGInputsOffTableP : Prop :=
  GGD4OddCentGraphInput ∧ GGD4OddCentInnerInput ∧ GGLieInnerDiagInput ∧ GGLieSU3FixedInput ∧
    GGTwE6InnerDiagInput

end Bundles

end CFSG.StandardType
