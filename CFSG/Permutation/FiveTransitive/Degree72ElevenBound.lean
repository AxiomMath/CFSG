module

public import CFSG.Permutation.FiveTransitive.AbelianOrbitEvaluation
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport
public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeOrbitSize

public section

namespace CFSG

namespace FiveTransitive.Degree72ElevenBound

open MulAction

private theorem eq_one_of_thirty_seven_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (q : Q) (hfixed : 37 ≤ (fixedBy X q).ncard) : q = 1 := by
  by_contra hq
  have hne : q.val.val ≠ 1 := fun he => hq (Subtype.ext (Subtype.ext he))
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
    hnotAlt q.val.property hne
  have he : fixedBy X q = Function.fixedPoints q.val.val := rfl
  rw [he, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    Equiv.Perm.card_fixedPoints, q.val.val.sum_cycleType, hcard] at hfixed
  rw [hcard] at hb
  omega

theorem card_le_cube
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 11 Q) [IsMulCommutative Q]
    (hfixed : Nat.card (fixedPoints Q X) = 6) : Nat.card Q ≤ 11 ^ 3 := by
  classical
  have hf : (fixedPoints Q X).ncard = 6 := by
    rw [← Nat.card_coe_set_eq, hfixed]
  have horbit : ∀ x : X, x ∉ fixedPoints Q X → (orbit Q x).ncard = 11 := by
    intro x hx
    rw [← Nat.card_coe_set_eq]
    exact Degree72LargePrimeOrbitSize.card_eq_prime 11 (by decide) hQ
      (by rw [Nat.card_eq_fintype_card,hcard]; decide) x hx
  have hout : ∀ s : Set X, s.ncard < 72 → ∃ x : X, x ∉ s := by
    intro s hs
    by_contra hn
    have he : s = Set.univ := Set.eq_univ_iff_forall.mpr (by simpa using hn)
    rw [he, Set.ncard_univ, Nat.card_eq_fintype_card, hcard] at hs
    omega
  obtain ⟨x, hx⟩ := hout (fixedPoints Q X) (by omega)
  have hox := horbit x hx
  have hdFx := AbelianOrbitEvaluation.orbit_disjoint_fixedPoints x hx
  have hcx : (fixedPoints Q X ∪ orbit Q x).ncard = 17 := by
    rw [Set.ncard_union_eq hdFx, hf, hox]
  obtain ⟨y, hy⟩ := hout (fixedPoints Q X ∪ orbit Q x) (by omega)
  have hyF : y ∉ fixedPoints Q X := fun h => hy (Or.inl h)
  have hyx : y ∉ orbit Q x := fun h => hy (Or.inr h)
  have hoy := horbit y hyF
  have hdFy := AbelianOrbitEvaluation.orbit_disjoint_fixedPoints y hyF
  have hdxy := AbelianOrbitEvaluation.orbit_disjoint_of_notMem x y hyx
  have hdSy : Disjoint (fixedPoints Q X ∪ orbit Q x) (orbit Q y) :=
    Set.disjoint_union_left.mpr ⟨hdFy, hdxy⟩
  have hcy : ((fixedPoints Q X ∪ orbit Q x) ∪ orbit Q y).ncard = 28 := by
    rw [Set.ncard_union_eq hdSy, hcx, hoy]
  obtain ⟨z, hz⟩ := hout ((fixedPoints Q X ∪ orbit Q x) ∪ orbit Q y) (by omega)
  have hzF : z ∉ fixedPoints Q X := fun h => hz (Or.inl (Or.inl h))
  have hzx : z ∉ orbit Q x := fun h => hz (Or.inl (Or.inr h))
  have hzy : z ∉ orbit Q y := fun h => hz (Or.inr h)
  have hoz := horbit z hzF
  have hdFz := AbelianOrbitEvaluation.orbit_disjoint_fixedPoints z hzF
  have hdxz := AbelianOrbitEvaluation.orbit_disjoint_of_notMem x z hzx
  have hdyz := AbelianOrbitEvaluation.orbit_disjoint_of_notMem y z hzy
  have hdSz : Disjoint ((fixedPoints Q X ∪ orbit Q x) ∪ orbit Q y) (orbit Q z) :=
    Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨hdFz, hdxz⟩, hdyz⟩
  have hcz : (((fixedPoints Q X ∪ orbit Q x) ∪ orbit Q y) ∪ orbit Q z).ncard = 39 := by
    rw [Set.ncard_union_eq hdSz, hcy, hoz]
  have hfree : ∀ q : Q, q • x = x → q • y = y → q • z = z → q = 1 := by
    intro q hqx hqy hqz
    apply eq_one_of_thirty_seven_fixed P hcard h5 hnotAlt Q q
    have hsub : ((fixedPoints Q X ∪ orbit Q x) ∪ orbit Q y) ∪ orbit Q z ⊆ fixedBy X q := by
      intro t ht
      rcases ht with ((ht | ht) | ht) | ht
      · exact ht q
      · exact AbelianOrbitEvaluation.orbit_subset_fixedBy q x hqx ht
      · exact AbelianOrbitEvaluation.orbit_subset_fixedBy q y hqy ht
      · exact AbelianOrbitEvaluation.orbit_subset_fixedBy q z hqz ht
    have hh := Set.ncard_le_ncard hsub
    rw [hcz] at hh
    omega
  have hb := AbelianOrbitEvaluation.card_le_three_orbits x y z hfree
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, hox, hoy, hoz] at hb
  exact hb

end FiveTransitive.Degree72ElevenBound

end CFSG
