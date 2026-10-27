module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

@[expose] def ggSuPairBlock (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ)
    (a b : Fin n) : Subgroup (Su K p f n) where
  carrier := {A | ∀ i j : Fin n, ((i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b)) →
    (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j = (1 : Matrix (Fin n) (Fin n) K) i j}
  mul_mem' := by
    intro A B hA hB i j hij
    have hAB : (((A * B : Su K p f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
      rfl
    rw [hAB, Matrix.mul_apply]
    rcases hij with hi | hj
    · rw [Finset.sum_eq_single i]
      · rw [hA i i (Or.inl hi)]
        rw [Matrix.one_apply_eq, one_mul]
        exact hB i j (Or.inl hi)
      · intro k _ hk
        rw [hA i k (Or.inl hi), Matrix.one_apply_ne (Ne.symm hk), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    · rw [Finset.sum_eq_single j]
      · rw [hB j j (Or.inr hj), Matrix.one_apply_eq, mul_one]
        exact hA i j (Or.inr hj)
      · intro k _ hk
        rw [hB k j (Or.inr hj), Matrix.one_apply_ne hk, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
  one_mem' := by
    intro i j _
    rfl
  inv_mem' := by
    intro A hA i j hij
    have hinv : (((A⁻¹ : Su K p f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        conjTr (unitaryInvolution K p f) ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      have h1 : conjTr (unitaryInvolution K p f) ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := A.2.2
      have h2 := Matrix.inv_eq_left_inv h1
      have h3 : (((A⁻¹ : Su K p f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹ := Matrix.coe_units_inv _
      rw [h3, h2]
    rw [hinv]
    have hji : (j ≠ a ∧ j ≠ b) ∨ (i ≠ a ∧ i ≠ b) := hij.symm
    have hA' := hA j i hji
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply]
    rw [hA']
    by_cases h : j = i
    · subst h
      rw [Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne h, map_zero, Matrix.one_apply_ne (Ne.symm h)]

@[expose] def GGTableBPosSU (p : ℕ) {G : Type} [Group G] (Bs X : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K 2] (f n : ℕ) (ψ : Su K 2 f n →* G) : Prop :=
  ∃ ε : Equiv.Perm (Fin n) ≃* ↥(ggAutomizer X Bs),
    (∀ a b : Fin n, a ≠ b →
      GGIsReflection p ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) ∧
    (∀ a b : Fin n, a ≠ b →
      ggRankOneIn X Bs ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
        (ggSuPairBlock K 2 f n a b).map ψ)

@[expose] def GGSecFiveNSKGPosAInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
        (∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X →
          ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (f n : ℕ) (ψ : Su K 2 f n →* G),
            Nat.card K = (2 ^ f) ^ 2 ∧ 4 ≤ n ∧ ψ.ker ≤ Subgroup.center (Su K 2 f n) ∧ ψ.range = X ∧
              p ∣ 2 ^ f + 1 ∧ GGTableBPosSU p Bs X K f n ψ ∧
              ∃ b : ℕ, n = b + 1 ∧ GGHasLabel ⟨.twA, b, f⟩ (↥X ⧸ Subgroup.center ↥X)

@[expose] def GGSecFiveRk1PhanAInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
            ∃ (F : Type) (_ : Field F) (_ : Finite F)
              (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G), CharP F 2 ∧
              Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧
              (∃ n ∈ ggRankOneIn X Bs r, n ∈ Subgroup.normalizer (Bs : Set G) ∧
                ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) ∧
              (GGSplitLie p X → p ∣ Nat.card F - 1) ∧
              (¬ GGSplitLie p X → p ∣ Nat.card F + 1) ∧
              ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
                GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → 2 ^ lab.n ≤ Nat.card F

end CFSG.StandardType

end
