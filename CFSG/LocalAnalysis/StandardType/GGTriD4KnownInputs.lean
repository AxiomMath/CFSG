module

public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeRepair
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Vocabulary

@[expose] def ggAutFixedSubgroup {R : Type*} [Group R] (σ : MulAut R) : Subgroup R where
  carrier := {r | σ r = r}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_ggAutFixedSubgroup {R : Type*} [Group R] (σ : MulAut R) (r : R) :
    r ∈ ggAutFixedSubgroup σ ↔ σ r = r :=
  Iff.rfl

@[expose] def GGLabelG2 (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .G2der

@[expose] def GGLabelA2 (lab : LargeEvenLabel) : Prop :=
  lab.rank = 2 ∧ 2 ≤ lab.n ∧
    ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1))

abbrev GGTriD4R (n : ℕ) (K : Type) [Field K] : Type :=
  LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)

abbrev GGTriD4ID (n : ℕ) (K : Type) [Field K] : Set (MulAut (GGTriD4R n K)) :=
  LargeEvenChevIDImage LargeEvenCartanD4 K (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)

end Vocabulary

section KnownGroup

@[expose] def GGTriD4InnDiag (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  I = Set.range (MulAut.conj : R →* MulAut R)

@[expose] def GGTriD4Schur (R : Type) [Group R] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ θ : X ⧸ Subgroup.center X ≃* R, Subgroup.center X = ⊥

@[expose] def GGTriD4AutRank (R : Type) [Group R] : Prop :=
  ∀ A : Subgroup (MulAut R), IsElemAbelian 3 A → Nat.card A ≤ 3 ^ 3

@[expose] def GGTriD4Components (R : Type) [Group R] : Prop :=
  ∀ σ : MulAut R, σ ^ 3 = 1 → σ ∉ (MulAut.conj : R →* MulAut R).range →
    ∀ Q : Subgroup R, IsComponentOf Q (ggAutFixedSubgroup σ) →
      Subgroup.center Q = ⊥ ∧
        (LargeEvenMarking Q (fun lab _ _ _ _ _ => GGLabelG2 lab) ∨
          LargeEvenMarking Q (fun lab _ _ _ _ _ => GGLabelA2 lab))

@[expose] def GGTriD4InnDiagInput : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 3 →
    IsSimpleGroup (GGTriD4R n K) → GGTriD4InnDiag (GGTriD4R n K) (GGTriD4ID n K)

@[expose] def GGTriD4SchurInput : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 3 →
    IsSimpleGroup (GGTriD4R n K) → GGTriD4Schur (GGTriD4R n K)

@[expose] def GGTriD4AutRankInput : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 3 →
    IsSimpleGroup (GGTriD4R n K) → GGTriD4AutRank (GGTriD4R n K)

@[expose] def GGTriD4ComponentsInput : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 3 →
    IsSimpleGroup (GGTriD4R n K) → GGTriD4Components (GGTriD4R n K)

@[expose] def GGTriD4KnownInput : Prop :=
  GGTriD4InnDiagInput ∧ GGTriD4SchurInput ∧ GGTriD4AutRankInput ∧ GGTriD4ComponentsInput

end KnownGroup

section StdSub

@[expose] def GGStdSubNotG2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp 3 B x L → LargeEvenStdSub 3 B x L D J →
      ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelG2 lab)

@[expose] def GGStdSubA2CentreInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp 3 B x L → LargeEvenStdSub 3 B x L D J → LargeEvenTwoLocalRank 3 G ≤ 4 →
      LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab) → Subgroup.center J = ⊥ →
        LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twE6 ∧ LargeEvenSplit 3 lab)

@[expose] def GGTriD4StdSubInput : Prop :=
  GGStdSubNotG2Input ∧ GGStdSubA2CentreInput

end StdSub

section TwE6

@[expose] def GGTwE6LocalRank (R : Type) [Group R] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ θ : X ⧸ Subgroup.center X ≃* R,
      ∃ U : Subgroup X, U ≠ ⊥ ∧ IsPGroup 2 U ∧
        ∃ E : Subgroup X, E ≤ Subgroup.normalizer (U : Set X) ∧ IsElemAbelian 3 E ∧
          (Nat.card E = 3 ^ 5 ∨ (Nat.card E = 3 ^ 4 ∧ E ⊓ Subgroup.center X = ⊥))

@[expose] def GGTwE6LocalRankInput : Prop :=
  ∀ n : ℕ, 1 ≤ n → 3 ∣ 2 ^ n + 1 → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 →
    IsSimpleGroup
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) →
    GGTwE6LocalRank
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))

end TwE6

end CFSG.StandardType
