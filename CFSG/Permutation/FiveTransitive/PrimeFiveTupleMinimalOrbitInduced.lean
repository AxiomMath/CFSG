module

public import CFSG.Permutation.FiveTransitive.ChosenTupleMinimalOrbitInduced
public import CFSG.Permutation.FiveTransitive.FaithfulNormalizerFixedDegree
public import CFSG.Permutation.FiveTransitive.PrimeTupleFixedCriterion

public section

namespace CFSG

namespace FiveTransitive.PrimeFiveTupleMinimalOrbitInduced

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent

theorem chosen
    {p : ℕ} [Fact p.Prime] {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (h5 : IsMultiplyPretransitive G X 5) (a : Fin 5 ↪ X)
    (P : Sylow p (stabilizer G a))
    (hfix : Nat.card (fixedPoints (ambientSylow a P) X) = 5)
    (x : X) (hx : x ∉ fixedPoints (ambientSylow a P) X)
    (hmin : ∀ y : X, y ∉ fixedPoints (ambientSylow a P) X →
      Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y)) :
    let A := ambientSylow a P
    let Q := (stabilizer A x).map A.subtype
    Q < A ∧ fixedPoints A X ⊂ fixedPoints Q X ∧
      6 ≤ Nat.card (Fixed (X := X) Q) ∧ Nat.card (Fixed (X := X) Q) % p = 5 % p ∧
      IsMultiplyPretransitive (Image (X := X) Q) (Fixed (X := X) Q) 5 ∧
      (∀ (b : Fin 5 ↪ Fixed (X := X) Q)
        (S : Sylow p (stabilizer (Image (X := X) Q) b)),
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
  obtain ⟨hQA, hstrict, hlocal⟩ := ChosenTupleMinimalOrbitInduced.local_geometry 5 (p := p) h5 a P x hx hmin
  have hA : IsPGroup p A := P.isPGroup'.map (stabilizer G a).subtype
  have hQ : IsPGroup p Q := (hA.to_subgroup (stabilizer A x)).map A.subtype
  have hparA := hA.card_modEq_card_fixedPoints X
  have hparQ := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % p = Nat.card (fixedPoints A X) % p at hparA
  change Nat.card X % p = Nat.card (fixedPoints Q X) % p at hparQ
  have hfixA : Nat.card (fixedPoints A X) = 5 := hfix
  have hmod : Nat.card (Fixed (X := X) Q) % p = 5 % p := by
    rw [fixed_eq]
    rw [hfixA] at hparA
    omega
  have hlt := Set.ncard_lt_ncard hstrict
  change (fixedPoints A X).ncard < (fixedPoints Q X).ncard at hlt
  have hlarge : 6 ≤ Nat.card (Fixed (X := X) Q) := by
    rw [fixed_eq,Nat.card_coe_set_eq]
    rw [Nat.card_coe_set_eq] at hfixA
    omega
  refine ⟨hQA, hstrict, hlarge, hmod, ?_, ?_, FaithfulNormalizerFixedDegree.degree_cases Q⟩
  · apply PrimeTupleFixedCriterion.multiply_of_tuple_sylow_fixed_card (p := p) 5
      hlarge
    intro b
    let S : Sylow p (stabilizer (Image (X := X) Q) b) := default
    exact ⟨S, (hlocal b S).2.1.trans hfix⟩
  · simpa only [hfix] using hlocal

end FiveTransitive.PrimeFiveTupleMinimalOrbitInduced

end CFSG
