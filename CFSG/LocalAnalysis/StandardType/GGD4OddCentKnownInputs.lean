module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Datum

@[expose] def GGOddCentDatum {X : Type*} [Group X] (A : Subgroup (MulAut X))
    (lab : LargeEvenLabel) {R : Type} [Group R] (I F : Set (MulAut R))
    (θ : X ⧸ Subgroup.center X ≃* R) : Prop :=
  lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n ∧ (Nat.card A = 3 ^ 4 → 3 ∣ lab.n) ∧
    (Nat.card A = 3 ^ 3 → ∀ a ∈ A, GGInnField I F (ggInducedAut θ a) → ggInducedAut θ a ∈ I) ∧
    ∃ a ∈ A, ¬ GGInnField I F (ggInducedAut θ a)

end Datum

section Neighbour

@[expose] def GGD4OddCentGraphInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
    ∀ (A : Subgroup (MulAut K)) (σ : MulAut K) (J : Subgroup K), GGKLocal A σ J →
      (Nat.card A = 3 ^ 3 ∨ Nat.card A = 3 ^ 4) →
        GGMarkingAll (K := K) fun lab _ _ I F θ =>
          GGOddCentDatum A lab I F θ → ¬ GGInnField I F (ggInducedAut θ σ) →
            LargeEvenMarking J fun lab' _ _ I' _ θ' =>
              GGLabelG2 lab' ∨ lab'.tag = .triD4 ∨
                (GGLabelA2 lab' ∧ lab'.tag = .twA ∧ Subgroup.center J = ⊥ ∧
                  (Nat.card A = 3 ^ 4 → ¬ GGAutsInduceOn A J θ' I'))

@[expose] def GGD4OddCentFieldInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
    ∀ (A : Subgroup (MulAut K)) (σ : MulAut K) (J : Subgroup K), GGKLocal A σ J →
      (Nat.card A = 3 ^ 3 ∨ Nat.card A = 3 ^ 4) →
        GGMarkingAll (K := K) fun lab _ _ I F θ =>
          GGOddCentDatum A lab I F θ → GGInnField I F (ggInducedAut θ σ) →
            ggInducedAut θ σ ∉ I →
              LargeEvenMarking J fun lab' _ _ I' _ θ' =>
                lab'.tag = .D ∧ lab'.rank = 4 ∧ Odd lab'.n ∧ ¬ GGAutsInduceOn A J θ' I'

@[expose] def GGD4OddCentInnerInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
    ∀ (A : Subgroup (MulAut K)) (σ : MulAut K) (J : Subgroup K), GGKLocal A σ J →
      (Nat.card A = 3 ^ 3 ∨ Nat.card A = 3 ^ 4) →
        GGMarkingAll (K := K) fun lab _ _ I F θ =>
          GGOddCentDatum A lab I F θ → ggInducedAut θ σ ∈ I →
            LargeEvenMarking J fun lab' _ _ I' _ θ' =>
              (GGLabelA2 lab' ∧ lab'.tag = .twA ∧ Subgroup.center J ≠ ⊥ ∧
                (GGAutsFixedInCenter A J ∨ ¬ GGAutsInduceOn A J θ' I')) ∨
              (lab'.tag = .A ∧ lab'.rank = 1)

end Neighbour

section TableP

@[expose] def GGStdSubNotTriD4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp 3 B x L → LargeEvenStdSub 3 B x L D J → LargeEvenTwoLocalRank 3 G ≤ 5 →
      ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .triD4)

@[expose] def GGStdSubNotA1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp 3 B x L → LargeEvenStdSub 3 B x L D J → LargeEvenTwoLocalRank 3 G ≤ 5 →
      ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1)

@[expose] def GGStdSubTwA2ScalarInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp 3 B x L → LargeEvenStdSub 3 B x L D J → LargeEvenTwoLocalRank 3 G ≤ 5 →
      LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA) →
      Subgroup.center J ≠ ⊥ →
        GGMarkingAll (K := ↥L) fun lab _ _ _ _ _ =>
          LargeEvenSplit 3 lab →
            (lab.tag = .twA ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ (lab.rank = 3 ∨ lab.rank = 4))

@[expose] def GGStdSubTwA2CentreInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp 3 B x L → LargeEvenStdSub 3 B x L D J → LargeEvenTwoLocalRank 3 G ≤ 5 →
      LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA) →
      Subgroup.center J = ⊥ →
        GGMarkingAll (K := ↥L) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab → lab.tag = .twE6

@[expose] def GGStdSubD4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp 3 B x L → LargeEvenStdSub 3 B x L D J → LargeEvenTwoLocalRank 3 G ≤ 5 →
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n) →
        GGMarkingAll (K := ↥L) fun lab _ _ _ _ _ =>
          LargeEvenSplit 3 lab → (lab.tag = .twD ∧ lab.rank = 5) ∨ lab.tag = .twE6

end TableP

section Component

@[expose] def GGLabelTwClassical (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∨ (lab.tag = .twA ∧ lab.rank = 3)

@[expose] def GGLieInnerDiagInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), GGAutLocal A δ J →
      LargeEvenMarking X (fun lab _ _ I _ θ => GGLabelTwClassical lab ∧ GGInducedInn A θ I) →
        GGMarkingAll (K := ↥J) fun _ _ _ I' _ θ' => GGAutsInduceOn A J θ' I'

@[expose] def GGLieSU3FixedInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), GGAutLocal A δ J →
      Subgroup.center J ≠ ⊥ →
      LargeEvenMarking X (fun lab _ _ I _ θ => GGLabelTwClassical lab ∧ GGInducedInn A θ I) →
      LargeEvenMarking J (fun lab' _ _ _ _ _ => GGLabelA2 lab' ∧ lab'.tag = .twA) →
        ¬ GGAutsFixedInCenter A J

@[expose] def GGTwE6InnerDiagInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), GGAutLocal A δ J →
      Nat.card A = 3 ^ 4 →
      (∃ U : Subgroup (MulAut X), U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U) →
      LargeEvenMarking X (fun lab _ _ I _ θ =>
        lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ GGInducedInn A θ I) →
        GGMarkingAll (K := ↥J) fun _ _ _ I' _ θ' => GGAutsInduceOn A J θ' I'

@[expose] def GGTwE6ThreeRank (R : Type) [Group R] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ θ : X ⧸ Subgroup.center X ≃* R,
      ∃ E : Subgroup X, IsElemAbelian 3 E ∧
        (Nat.card E = 3 ^ 6 ∨ (Nat.card E = 3 ^ 5 ∧ E ⊓ Subgroup.center X = ⊥))

@[expose] def GGTwE6ThreeRankInput : Prop :=
  ∀ n : ℕ, 1 ≤ n → 3 ∣ 2 ^ n + 1 → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 →
    IsSimpleGroup
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) →
    GGTwE6ThreeRank
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))

end Component

section Bundle

@[expose] def GGD4OddCentKGInputs : Prop :=
  GGD4OddCentGraphInput ∧ GGD4OddCentFieldInput ∧ GGD4OddCentInnerInput ∧
    GGStdSubNotTriD4Input ∧ GGStdSubNotA1Input ∧ GGStdSubTwA2ScalarInput ∧
    GGStdSubTwA2CentreInput ∧ GGStdSubD4Input ∧ GGLieInnerDiagInput ∧ GGLieSU3FixedInput ∧
    GGTwE6InnerDiagInput ∧ GGTwE6ThreeRankInput

end Bundle

end CFSG.StandardType
