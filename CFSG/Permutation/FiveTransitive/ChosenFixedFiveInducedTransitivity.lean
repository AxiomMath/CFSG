module

public import CFSG.Permutation.FiveTransitive.ChosenTupleMinimalOrbitInduced
public import CFSG.Permutation.FiveTransitive.TupleSylowExactTransitivity
public import CFSG.Permutation.FiveTransitive.FaithfulNormalizerFixedDegree

public section

namespace CFSG

namespace FiveTransitive.ChosenFixedFiveInducedTransitivity

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent

theorem chosen_five
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (h5 : IsMultiplyPretransitive G X 5) (a : Fin 5 ↪ X)
    (P : Sylow 2 (stabilizer G a))
    (hfix : Nat.card (fixedPoints (ambientSylow a P) X) = 5)
    (x : X) (hx : x ∉ fixedPoints (ambientSylow a P) X)
    (hmin : ∀ y : X, y ∉ fixedPoints (ambientSylow a P) X →
      Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y)) :
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
        (Q ≠ ⊥ ∧ Nat.card (Fixed (X := X) Q) < Nat.card X)) := by
  classical
  let A := ambientSylow a P
  let Q := (stabilizer A x).map A.subtype
  obtain ⟨hQA, hstrict, hlocal⟩ := ChosenTupleMinimalOrbitInduced.local_geometry 5 h5 a P x hx hmin
  have hA : IsPGroup 2 A := P.isPGroup'.map (stabilizer G a).subtype
  have hQ : IsPGroup 2 Q := (hA.to_subgroup (stabilizer A x)).map A.subtype
  have hparA := hA.card_modEq_card_fixedPoints X
  have hparQ := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % 2 = Nat.card (fixedPoints A X) % 2 at hparA
  change Nat.card X % 2 = Nat.card (fixedPoints Q X) % 2 at hparQ
  have hfixA : Nat.card (fixedPoints A X) = 5 := hfix
  rw [hfixA] at hparA
  have hodd : Odd (Nat.card (Fixed (X := X) Q)) := by
    rw [fixed_eq, Nat.odd_iff]
    omega
  have hlt := Set.ncard_lt_ncard hstrict
  change (fixedPoints A X).ncard < (fixedPoints Q X).ncard at hlt
  have hlarge : 7 ≤ Nat.card (Fixed (X := X) Q) := by
    rw [fixed_eq, Nat.card_coe_set_eq] at hodd ⊢
    rw [Nat.card_coe_set_eq] at hfixA
    have ho := hodd
    rw [Nat.odd_iff] at ho
    omega
  refine ⟨hQA, hstrict, hlarge, hodd, ?_, ?_, FaithfulNormalizerFixedDegree.degree_cases Q⟩
  · apply TupleSylowExactTransitivity.multiply_of_tuple_sylow_fixed_card 5
      ((by decide : 6 ≤ 7).trans hlarge)
    intro b
    let S : Sylow 2 (stabilizer (Image (X := X) Q) b) := default
    exact ⟨S, (hlocal b S).2.1.trans hfix⟩
  · simpa only [hfix] using hlocal

theorem exists_five
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (h5 : IsMultiplyPretransitive G X 5) (a : Fin 5 ↪ X)
    (P : Sylow 2 (stabilizer G a)) (hP : (P : Subgroup (stabilizer G a)) ≠ ⊥)
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
          (Q ≠ ⊥ ∧ Nat.card (Fixed (X := X) Q) < Nat.card X)) := by
  obtain ⟨x, hx, hmin, _⟩ := ChosenTupleMinimalOrbitInduced.exists_local_geometry 5 h5 a P hP
  exact ⟨x, hx, hmin, chosen_five h5 a P hfix x hx hmin⟩

end FiveTransitive.ChosenFixedFiveInducedTransitivity

end CFSG
