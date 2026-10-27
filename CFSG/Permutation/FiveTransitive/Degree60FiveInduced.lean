module

public import CFSG.Permutation.FiveTransitive.Degree60FiveFixedCriterion
public import CFSG.Permutation.FiveTransitive.ChosenTupleMinimalOrbitInduced
public import CFSG.Permutation.FiveTransitive.FaithfulNormalizerFixedDegree

public section

namespace CFSG

namespace FiveTransitive.Degree60FiveInduced

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent

theorem chosen_five
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (h5 : IsMultiplyPretransitive G X 5) (a : Fin 5 ↪ X)
    (P : Sylow 5 (stabilizer G a))
    (hfix : Nat.card (fixedPoints (ambientSylow a P) X) = 5)
    (x : X) (hx : x ∉ fixedPoints (ambientSylow a P) X)
    (hmin : ∀ y : X, y ∉ fixedPoints (ambientSylow a P) X →
      Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y)) :
    let A := ambientSylow a P
    let Q := (stabilizer A x).map A.subtype
    Q < A ∧ fixedPoints A X ⊂ fixedPoints Q X ∧
      10 ≤ Nat.card (Fixed (X := X) Q) ∧ 5 ∣ Nat.card (Fixed (X := X) Q) ∧
      IsMultiplyPretransitive (Image (X := X) Q) (Fixed (X := X) Q) 5 ∧
      (∀ (b : Fin 5 ↪ Fixed (X := X) Q)
        (S : Sylow 5 (stabilizer (Image (X := X) Q) b)),
      let T := (S : Subgroup (stabilizer (Image (X := X) Q) b)).map
        (stabilizer (Image (X := X) Q) b).subtype
      T ≠ ⊥ ∧ Nat.card (fixedPoints T (Fixed (X := X) Q)) = 5 ∧
        ∀ t : Image (X := X) Q, t ∈ T → t ≠ 1 →
          ∀ z : Fixed (X := X) Q, z ∉ fixedPoints T (Fixed (X := X) Q) → t • z ≠ z) ∧
      ((Q = ⊥ ∧ Nat.card (Fixed (X := X) Q) = Nat.card X) ∨
        (Q ≠ ⊥ ∧ Nat.card (Fixed (X := X) Q) < Nat.card X)) := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let A := ambientSylow a P
  let Q := (stabilizer A x).map A.subtype
  obtain ⟨hQA, hstrict, hlocal⟩ := ChosenTupleMinimalOrbitInduced.local_geometry 5 h5 a P x hx hmin
  have hA : IsPGroup 5 A := P.isPGroup'.map (stabilizer G a).subtype
  have hQ : IsPGroup 5 Q := (hA.to_subgroup (stabilizer A x)).map A.subtype
  have hparA := hA.card_modEq_card_fixedPoints X
  have hparQ := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % 5 = Nat.card (fixedPoints A X) % 5 at hparA
  change Nat.card X % 5 = Nat.card (fixedPoints Q X) % 5 at hparQ
  have hfixA : Nat.card (fixedPoints A X) = 5 := hfix
  rw [hfixA] at hparA
  have hodd : 5 ∣ Nat.card (Fixed (X := X) Q) := by
    rw [fixed_eq, Nat.dvd_iff_mod_eq_zero]
    omega
  have hlt := Set.ncard_lt_ncard hstrict
  change (fixedPoints A X).ncard < (fixedPoints Q X).ncard at hlt
  have hlarge : 10 ≤ Nat.card (Fixed (X := X) Q) := by
    rw [fixed_eq, Nat.card_coe_set_eq] at hodd ⊢
    rw [Nat.card_coe_set_eq] at hfixA
    have ho := hodd
    rw [Nat.dvd_iff_mod_eq_zero] at ho
    omega
  refine ⟨hQA, hstrict, hlarge, hodd, ?_, ?_, FaithfulNormalizerFixedDegree.degree_cases Q⟩
  · apply Degree60FiveFixedCriterion.multiply_of_tuple_sylow_fixed_card 5
      ((by decide : 6 ≤ 10).trans hlarge)
    intro b
    let S : Sylow 5 (stabilizer (Image (X := X) Q) b) := default
    exact ⟨S, (hlocal b S).2.1.trans hfix⟩
  · simpa only [hfix] using hlocal

end FiveTransitive.Degree60FiveInduced

end CFSG
