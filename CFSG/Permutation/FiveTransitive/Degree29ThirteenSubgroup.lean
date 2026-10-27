module

public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixedBounds
public import CFSG.Permutation.FiveTransitive.PrimePowerSmallDegree
public import CFSG.Permutation.FiveTransitive.FreeComplementCard

public section

namespace CFSG

namespace FiveTransitive.Degree29ThirteenSubgroup

open MulAction

theorem order_thirteen_cycle_type
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 29)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = 13) :
    (u : Equiv.Perm X).cycleType = {13, 13} := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 13 := (Subgroup.orderOf_coe u).trans huorder
  have hgprime : (orderOf g).Prime := by rw [hgorder]; norm_num
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, hgorder] at hsum
  have hle : g.support.card ≤ 29 := hcard ▸ Finset.card_le_univ g.support
  have hne : g ≠ 1 := by intro h; simp [h] at hgorder
  have hmin := HighDegreeManningSupport.degree_le_two_mul_support
    P (by omega) h5 hnotAlt u.prop hne
  rw [hcard] at hmin
  have hkTwo : k + 1 = 2 := by change 29 ≤ 2 * g.support.card at hmin; omega
  change g.cycleType = _
  rw [hk, hgorder, hkTwo]
  norm_num

theorem fixed_card_eq_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 29)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 13 Q) (hne : Q ≠ ⊥) :
    Nat.card (fixedPoints Q X) = 3 := by
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hu := MinimalOrbitFixedBounds.fixed_card_le_half X P (by omega) h5 hnotAlt Q hne
  rw [hcard] at hu
  have hm := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % 13 = Nat.card (fixedPoints Q X) % 13 at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  omega

private theorem element_fixed_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 29)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 13 Q) (q : Q) (hq : q ≠ 1) :
    Nat.card (Function.fixedPoints q.val.val) = 3 := by
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨e,he⟩ := IsPGroup.iff_orderOf.mp hQ q
  have hp := PrimePowerSmallDegree.pow_eq_one (by norm_num : Nat.Prime 13)
    (by rw [hcard]; norm_num) q.val.val ⟨e,by
      rw [Subgroup.orderOf_coe q.val,Subgroup.orderOf_coe q,he]⟩
  have hqpow : q ^ 13 = 1 := Subtype.ext (Subtype.ext hp)
  have horder : orderOf q.val = 13 := (Subgroup.orderOf_coe q).trans (orderOf_eq_prime hqpow hq)
  have htype := order_thirteen_cycle_type P hcard h5 hnotAlt q.val horder
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,htype,hcard]
  norm_num

theorem card_eq_thirteen
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 29)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 13 Q) (hne : Q ≠ ⊥) : Nat.card Q = 13 := by
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hfixed := fixed_card_eq_three P hcard h5 hnotAlt Q hQ hne
  have hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1 := by
    intro q x hx hqx
    by_contra hq
    have helem := element_fixed_card P hcard h5 hnotAlt Q hQ q hq
    have hsub : fixedPoints Q X ⊆ Function.fixedPoints q.val.val := fun x hx => hx q
    have heq : fixedPoints Q X = Function.fixedPoints q.val.val :=
      Set.eq_of_subset_of_ncard_le hsub (by
        rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hfixed,helem])
    exact hx (heq.symm ▸ hqx)
  have hd := FreeComplementCard.card_dvd_complement Q X (fixedPoints Q X)
    (fun q x hx => (hx q).symm ▸ hx) hfree
  rw [← Nat.card_coe_set_eq,hfixed,Nat.card_eq_fintype_card (α := X),hcard] at hd
  have hle : Nat.card Q ≤ 26 := Nat.le_of_dvd (by norm_num) hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he1 : e ≤ 1 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 13) (by omega : 2 ≤ e)
    norm_num at hh
    omega
  have he0 : e ≠ 0 := by
    intro hz
    rw [hz,pow_zero] at he
    exact hne (Subgroup.card_eq_one.mp he)
  have heq : e = 1 := by omega
  simpa only [heq,pow_one] using he

end FiveTransitive.Degree29ThirteenSubgroup

end CFSG
