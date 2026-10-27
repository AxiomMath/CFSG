module

public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixedBounds
public import CFSG.Permutation.FiveTransitive.PrimePowerSmallDegree
public import CFSG.Permutation.FiveTransitive.FreeComplementCard

public section

namespace CFSG

namespace FiveTransitive.TwoPrimeCycleSubgroup

open MulAction

theorem order_prime_cycle_type
    {X : Type} [Fintype X] [DecidableEq X]
    (p f : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) (hf : f = 3 ∨ f = 4)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 2 * p + f)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = p) : u.val.cycleType = {p,p} := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = p := (Subgroup.orderOf_coe u).trans huorder
  obtain ⟨k,hk⟩ := Equiv.Perm.cycleType_prime_order (σ := g) (by rwa [hgorder])
  have hsum := g.sum_cycleType
  rw [hk,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hgorder] at hsum
  have hle : g.support.card ≤ 2 * p + f := hcard ▸ Finset.card_le_univ g.support
  have hne : g ≠ 1 := by intro h; rw [h,orderOf_one] at hgorder; omega
  have hmin := HighDegreeManningSupport.degree_le_two_mul_support
    P (by omega) h5 hnotAlt u.property hne
  rw [hcard] at hmin
  change 2 * p + f ≤ 2 * g.support.card at hmin
  have hlt : (k + 1) * p < 3 * p := by rw [hsum]; omega
  have hk3 : k + 1 < 3 := (Nat.mul_lt_mul_right hp.pos).mp hlt
  have hk2 : k + 1 = 2 := by
    by_contra hn
    have he : k + 1 = 1 := by omega
    rw [he,one_mul] at hsum
    omega
  change g.cycleType = _
  rw [hk,hgorder,hk2]
  simp

theorem fixed_card
    {X : Type} [Fintype X] [DecidableEq X]
    (p f : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) (hf : f = 3 ∨ f = 4)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 2 * p + f)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup p Q) (hne : Q ≠ ⊥) :
    Nat.card (fixedPoints Q X) = f := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hu := MinimalOrbitFixedBounds.fixed_card_le_half X P (by omega) h5 hnotAlt Q hne
  rw [hcard] at hu
  have hm := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % p = Nat.card (fixedPoints Q X) % p at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  have hfp : f < p := by omega
  have hmod : Nat.card (fixedPoints Q X) % p = f := by
    rw [← hm]
    simp [Nat.add_mod,Nat.mod_eq_of_lt hfp]
  by_cases hlt : Nat.card (fixedPoints Q X) < p
  · rwa [Nat.mod_eq_of_lt hlt] at hmod
  · have hge : p ≤ Nat.card (fixedPoints Q X) := by omega
    rw [Nat.mod_eq_sub_mod hge,Nat.mod_eq_of_lt (show Nat.card (fixedPoints Q X) - p < p by omega)] at hmod
    omega

private theorem element_fixed_card
    {X : Type} [Fintype X] [DecidableEq X]
    (p f : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) (hf : f = 3 ∨ f = 4)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 2 * p + f)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup p Q) (q : Q) (hq : q ≠ 1) :
    Nat.card (Function.fixedPoints q.val.val) = f := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨e,he⟩ := IsPGroup.iff_orderOf.mp hQ q
  have hdegree : Fintype.card X < p ^ 2 := by
    rw [hcard]
    have hmul := Nat.mul_le_mul_right p hp13
    nlinarith [show f ≤ 4 by omega]
  have hpow := PrimePowerSmallDegree.pow_eq_one hp hdegree q.val.val ⟨e,by
    rw [Subgroup.orderOf_coe q.val,Subgroup.orderOf_coe q,he]⟩
  have hqpow : q ^ p = 1 := Subtype.ext (Subtype.ext hpow)
  have horder : orderOf q.val = p := (Subgroup.orderOf_coe q).trans (orderOf_eq_prime hqpow hq)
  have htype := order_prime_cycle_type p f hp hp13 hf P hcard h5 hnotAlt q.val horder
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,htype,hcard]
  change 2 * p + f - (p + p) = f
  omega

theorem card_eq_prime
    {X : Type} [Fintype X] [DecidableEq X]
    (p f : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) (hf : f = 3 ∨ f = 4)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 2 * p + f)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup p Q) (hne : Q ≠ ⊥) : Nat.card Q = p := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hfixed := fixed_card p f hp hp13 hf P hcard h5 hnotAlt Q hQ hne
  have hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1 := by
    intro q x hx hqx
    by_contra hq
    have helem := element_fixed_card p f hp hp13 hf P hcard h5 hnotAlt Q hQ q hq
    have hsub : fixedPoints Q X ⊆ Function.fixedPoints q.val.val := fun x hx => hx q
    have heq : fixedPoints Q X = Function.fixedPoints q.val.val :=
      Set.eq_of_subset_of_ncard_le hsub (by
        rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hfixed,helem])
    exact hx (heq.symm ▸ hqx)
  have hd := FreeComplementCard.card_dvd_complement Q X (fixedPoints Q X)
    (fun q x hx => (hx q).symm ▸ hx) hfree
  rw [← Nat.card_coe_set_eq,hfixed,Nat.card_eq_fintype_card (α := X),hcard,Nat.add_sub_cancel] at hd
  have hle : Nat.card Q ≤ 2 * p := Nat.le_of_dvd (by omega) hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he1 : e ≤ 1 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right hp.pos (by omega : 2 ≤ e)
    rw [← he] at hh
    have hmul := Nat.mul_le_mul_right p hp13
    nlinarith
  have he0 : e ≠ 0 := by
    intro hz
    rw [hz,pow_zero] at he
    exact hne (Subgroup.card_eq_one.mp he)
  have heq : e = 1 := by omega
  simpa only [heq,pow_one] using he

end FiveTransitive.TwoPrimeCycleSubgroup

end CFSG
