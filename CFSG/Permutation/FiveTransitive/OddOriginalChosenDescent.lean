module

public import CFSG.Permutation.FiveTransitive.OddOriginalTupleEntrance
public import CFSG.Permutation.FiveTransitive.HighDegreeFixedFiveInducedDescent
public import CFSG.Permutation.FiveTransitive.MinimalOrbitBottomSemiregular

public section

namespace CFSG

namespace FiveTransitive.OddOriginalChosenDescent

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent

theorem exists_descent
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (hodd : Odd (Fintype.card X)) (a : Fin 5 ↪ X)
    (P : Sylow 2 (stabilizer G a)) :
    (P : Subgroup (stabilizer G a)) ≠ ⊥ ∧
      fixedPoints (ambientSylow a P) X = Set.range a ∧
      ∃ x : X, x ∉ Set.range a ∧
        (∀ y : X, y ∉ Set.range a →
          Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y)) ∧
        let A := ambientSylow a P
        let Q := (stabilizer A x).map A.subtype
        Q < A ∧ fixedPoints A X ⊂ fixedPoints Q X ∧
          7 ≤ Nat.card (Fixed (X := X) Q) ∧ Odd (Nat.card (Fixed (X := X) Q)) ∧
          IsMultiplyPretransitive (Image (X := X) Q) (Fixed (X := X) Q) 5 ∧
          FaithfulSMul (Image (X := X) Q) (Fixed (X := X) Q) ∧
          (∀ (b : Fin 5 ↪ Fixed (X := X) Q)
            (S : Sylow 2 (stabilizer (Image (X := X) Q) b)),
          let T := (S : Subgroup (stabilizer (Image (X := X) Q) b)).map
            (stabilizer (Image (X := X) Q) b).subtype
          T ≠ ⊥ ∧ Nat.card (fixedPoints T (Fixed (X := X) Q)) = 5 ∧
            ∀ t : Image (X := X) Q, t ∈ T → t ≠ 1 →
              ∀ z : Fixed (X := X) Q, z ∉ fixedPoints T (Fixed (X := X) Q) → t • z ≠ z) ∧
          ((Q = ⊥ ∧ Nat.card (Fixed (X := X) Q) = Nat.card X ∧
            ∀ q : G, q ∈ A → q ≠ 1 → ∀ y : X, y ∉ Set.range a → q • y ≠ y) ∨
            (Q ≠ ⊥ ∧ Nat.card (Fixed (X := X) Q) < Nat.card X ∧
              Nat.card (Fixed (X := X) Q) ≤ Fintype.card X / 2)) := by
  obtain ⟨hP, hfixed⟩ := OddOriginalTupleEntrance.entrance X G hcard h5 hnotAlt hodd a P
  have hfix : Nat.card (fixedPoints (ambientSylow a P) X) = 5 := by
    rw [hfixed, Nat.card_coe_set_eq, Set.ncard_range_of_injective a.injective, Nat.card_fin]
  obtain ⟨x, hx, hmin, hQA, hstrict, hlarge, hoddQ, hJ5, hlocal, hcases⟩ :=
    HighDegreeFixedFiveInducedDescent.exists_five_with_half_bound
      X G hcard h5 hnotAlt a P hP hfix
  refine ⟨hP, hfixed, x, ?_, ?_, hQA, hstrict, hlarge, hoddQ, hJ5, inferInstance, hlocal, ?_⟩
  · rwa [hfixed] at hx
  · simpa only [hfixed] using hmin
  · rcases hcases with ⟨hbot, hdegree⟩ | hnonbot
    · refine Or.inl ⟨hbot, hdegree, ?_⟩
      simpa only [hfixed] using MinimalOrbitBottomSemiregular.semiregular_of_bottom
        (ambientSylow a P) x hmin hbot
    · exact Or.inr hnonbot

end FiveTransitive.OddOriginalChosenDescent

end CFSG
