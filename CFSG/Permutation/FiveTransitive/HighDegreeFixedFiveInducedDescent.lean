module

public import CFSG.Permutation.FiveTransitive.ChosenFixedFiveInducedTransitivity
public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixedBounds

public section

namespace CFSG

namespace FiveTransitive.HighDegreeFixedFiveInducedDescent

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent

theorem exists_five_with_half_bound
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (a : Fin 5 ↪ X) (P : Sylow 2 (stabilizer G a))
    (hP : (P : Subgroup (stabilizer G a)) ≠ ⊥)
    (hfix : Nat.card (fixedPoints (ambientSylow a P) X) = 5) :
    ∃ x : X, x ∉ fixedPoints (ambientSylow a P) X ∧
      (∀ y : X, y ∉ fixedPoints (ambientSylow a P) X →
        Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y)) ∧
      let A := ambientSylow a P
      let Q := (stabilizer A x).map A.subtype
      Q < A ∧ fixedPoints A X ⊂ fixedPoints Q X ∧
        7 ≤ Nat.card (Fixed (X := X) Q) ∧ Odd (Nat.card (Fixed (X := X) Q)) ∧
        IsMultiplyPretransitive (Image (X := X) Q) (Fixed (X := X) Q) 5 ∧
        (∀ (b : Fin 5 ↪ Fixed (X := X) Q)
          (S : Sylow 2 (stabilizer (Image (X := X) Q) b)),
        let T := (S : Subgroup (stabilizer (Image (X := X) Q) b)).map
          (stabilizer (Image (X := X) Q) b).subtype
        T ≠ ⊥ ∧ Nat.card (fixedPoints T (Fixed (X := X) Q)) = 5 ∧
          ∀ t : Image (X := X) Q, t ∈ T → t ≠ 1 →
            ∀ z : Fixed (X := X) Q, z ∉ fixedPoints T (Fixed (X := X) Q) → t • z ≠ z) ∧
        ((Q = ⊥ ∧ Nat.card (Fixed (X := X) Q) = Nat.card X) ∨
          (Q ≠ ⊥ ∧ Nat.card (Fixed (X := X) Q) < Nat.card X ∧
            Nat.card (Fixed (X := X) Q) ≤ Fintype.card X / 2)) := by
  obtain ⟨x, hx, hmin, hQA, hstrict, hlarge, hodd, hJ5, hlocal, hcases⟩ :=
    ChosenFixedFiveInducedTransitivity.exists_five h5 a P hP hfix
  refine ⟨x, hx, hmin, hQA, hstrict, hlarge, hodd, hJ5, hlocal, ?_⟩
  rcases hcases with hbot | ⟨hne, hlt⟩
  · exact Or.inl hbot
  · refine Or.inr ⟨hne, hlt, ?_⟩
    rw [fixed_eq]
    exact MinimalOrbitFixedBounds.fixed_card_le_half X G hcard h5 hnotAlt _ hne

end FiveTransitive.HighDegreeFixedFiveInducedDescent

end CFSG
