module

public import CFSG.RankThree.Lattice.SteinbergBIOrbitLattice
public import CFSG.LieType.Chevalley.RelativeWeylTwist

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix

@[expose] def CyclicSylowConclusion' (C : Type) [Group C] (p n₀ d : ℕ) : Prop :=
  ∃ T : Subgroup C, IsCyclic T ∧ Nat.card T ∣ n₀ ∧ n₀ / Nat.card T ∣ d ∧
    (∃ S : Sylow p C, (S : Subgroup C) ≤ T) ∧
    (∀ Q : Subgroup C, IsPGroup p Q → IsCyclic Q) ∧
    (∀ x : C, orderOf x = p → ∃ g : C, g * x * g⁻¹ ∈ T) ∧
    (∀ x : C, orderOf x = p → ∃ g : C, g * x * g⁻¹ ∈ T ∧
      Subgroup.centralizer {g * x * g⁻¹} = T)

abbrev CyclicSylowConclusion (τ : Tag) (K : Type) [Field K] (p n₀ d : ℕ) : Prop :=
  CyclicSylowConclusion' (adjointGroup τ K) p n₀ d

@[expose] def IsWeylMatrix (τ : Tag) (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) : Prop :=
  ∃ w : WeylGroup τ, ∀ u, w • u = M *ᵥ u

@[expose] def CyclicTorusStatement (τ : Tag) (d p₀ : ℕ) : Prop :=
  ∀ M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ, IsWeylMatrix τ M →
    ∀ v : Fin τ.rank → ℤ,
      LinearIndependent ℤ (fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v) →
      Submodule.span ℤ (Set.range fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v) = ⊤ →
      (M.charpoly.coeff 0 = 1 ∨ M.charpoly.coeff 0 = -1) →
      ∀ (K : Type) [Field K] [Finite K] (p : ℕ), p.Prime → p₀ < p → ¬ p ∣ Nat.card K →
        M.charpoly.eval (Nat.card K : ℤ) ≠ 0 →
        (∀ α : Fin τ.rank → ℤ, IsRoot τ α → ∃ A : ℤ[X],
          (∀ β, (aeval M A) *ᵥ β ∈ orbitLattice M α) ∧ ¬ (p : ℤ) ∣ A.eval (Nat.card K : ℤ)) →
        p ^ (Nat.card (adjointGroup τ K)).factorization p =
          p ^ (M.charpoly.eval (Nat.card K : ℤ)).natAbs.factorization p →
        CyclicSylowConclusion τ K p (M.charpoly.eval (Nat.card K : ℤ)).natAbs d

@[expose] def CyclicTorusTheorem : Prop :=
  ∀ (τ : Tag) (d : ℕ), ((τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) →
    CyclicTorusStatement τ d 7

@[expose] def CyclicTorusTheoremF4 : Prop := CyclicTorusStatement .F4 1 3

theorem wordProd_smul_eq_wordMat_mulVec (τ : Tag) (l : List (Fin τ.rank))
    (u : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd l • u = wordMat τ l *ᵥ u := by
  rw [wordProd_smul]
  induction l with
  | nil => rw [List.foldr_nil, wordMat_nil, one_mulVec]
  | cons i l ih => rw [List.foldr_cons, ih, wordMat_cons, ← mulVec_mulVec, reflMat_mulVec]

theorem IsWeylMatrix.of_word (τ : Tag) (l : List (Fin τ.rank)) : IsWeylMatrix τ (wordMat τ l) :=
  ⟨(coxeterSystem τ).wordProd l, wordProd_smul_eq_wordMat_mulVec τ l⟩

theorem IsWeylMatrix.mul {τ : Tag} {M N : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hM : IsWeylMatrix τ M) (hN : IsWeylMatrix τ N) : IsWeylMatrix τ (M * N) := by
  obtain ⟨w, hw⟩ := hM
  obtain ⟨w', hw'⟩ := hN
  exact ⟨w * w', fun u => by rw [mul_smul, hw', hw, Matrix.mulVec_mulVec]⟩

theorem IsWeylMatrix.one (τ : Tag) : IsWeylMatrix τ (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) :=
  ⟨1, fun u => by rw [one_smul, Matrix.one_mulVec]⟩

theorem IsWeylMatrix.pow {τ : Tag} {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hM : IsWeylMatrix τ M) (k : ℕ) : IsWeylMatrix τ (M ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact IsWeylMatrix.one τ
  | succ k ih => rw [pow_succ]; exact ih.mul hM

end CFSG.RankThree.PartOne.KE
