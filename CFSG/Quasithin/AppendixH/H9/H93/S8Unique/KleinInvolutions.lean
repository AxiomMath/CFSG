module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.ASVolI.ChH

open Equiv

private def sortedElems (A : Finset (Fin 8)) : List (Fin 8) :=
  (List.finRange 8).filter (· ∈ A)

def kleinInvolution (A : Finset (Fin 8)) (i : Fin 3) : Perm (Fin 8) :=
  match sortedElems A with
  | a :: b :: c :: d :: _ =>
    if i = 0 then swap a b * swap c d
    else if i = 1 then swap a c * swap b d
    else swap a d * swap b c
  | _ => 1

private theorem kleinInvolution_spec_aux :
    ∀ A ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin 8)), ∀ i : Fin 3, ∀ y : Fin 8,
      (y ∈ A → kleinInvolution A i y ∈ A ∧ kleinInvolution A i y ≠ y ∧
        kleinInvolution A i (kleinInvolution A i y) = y) ∧
      (y ∉ A → kleinInvolution A i y = y) := by
  decide +kernel

theorem kleinInvolution_spec {A : Finset (Fin 8)} (hA : A.card = 4) (i : Fin 3) {y : Fin 8}
    (hy : y ∈ A) :
    kleinInvolution A i y ∈ A ∧ kleinInvolution A i y ≠ y ∧
      kleinInvolution A i (kleinInvolution A i y) = y :=
  ((kleinInvolution_spec_aux A (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA⟩) i y).1 hy)

theorem kleinInvolution_apply_of_notMem {A : Finset (Fin 8)} (hA : A.card = 4) (i : Fin 3)
    {y : Fin 8} (hy : y ∉ A) : kleinInvolution A i y = y :=
  ((kleinInvolution_spec_aux A (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA⟩) i y).2 hy)

private def OrderThree (σ : Perm (Fin 8)) : Prop := σ * σ * σ = 1 ∧ σ ≠ 1

private instance (σ : Perm (Fin 8)) : Decidable (OrderThree σ) :=
  inferInstanceAs (Decidable (σ * σ * σ = 1 ∧ σ ≠ 1))

private theorem exists_orderThree_aux :
    ∀ A ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin 8)), (0 : Fin 8) ∈ A →
    ∀ B ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin 8)), (0 : Fin 8) ∈ B → A ≠ B →
      ∃ i j : Fin 3, OrderThree (kleinInvolution A i * kleinInvolution B j) ∨
        OrderThree (kleinInvolution A i * kleinInvolution Bᶜ j) := by
  decide +kernel

theorem exists_kleinInvolution_mul_order_three {A B : Finset (Fin 8)} (hA : A.card = 4)
    (hB : B.card = 4) (hA0 : (0 : Fin 8) ∈ A) (hB0 : (0 : Fin 8) ∈ B) (hAB : A ≠ B) :
    ∃ C : Finset (Fin 8), (C = B ∨ C = Bᶜ) ∧ ∃ i j : Fin 3,
      (kleinInvolution A i * kleinInvolution C j) ^ 3 = 1 ∧
        kleinInvolution A i * kleinInvolution C j ≠ 1 := by
  obtain ⟨i, j, h⟩ := exists_orderThree_aux A
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA⟩) hA0 B
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hB⟩) hB0 hAB
  rcases h with h | h
  · exact ⟨B, Or.inl rfl, i, j, by rw [pow_three']; exact h.1, h.2⟩
  · exact ⟨Bᶜ, Or.inr rfl, i, j, by rw [pow_three']; exact h.1, h.2⟩

end CFSG.ASVolI.ChH
