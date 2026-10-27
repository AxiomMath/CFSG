module

public import CFSG.Permutation.FiveTransitive.Degree36FiveCentralizerSupport
public import CFSG.Permutation.FiveTransitive.FreeComplementCard

public section

namespace CFSG

namespace FiveTransitive.Degree36FiveCentralizerSemiregular

open MulAction

private theorem order_five_fixedPoints_eq
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hfixed : Nat.card (fixedPoints Q X) = 6)
    (h9 : 9 ∣ Nat.card (Subgroup.centralizer (Q : Set P)))
    (u : Q) (huorder : orderOf u = 5) :
    fixedPoints Q X = Function.fixedPoints u.val.val := by
  have hsupp := Degree36FiveCentralizerSupport.order_five_support_card
    P hcard h5 hnotAlt Q (by omega) h9 u huorder
  have hsub : fixedPoints Q X ⊆ Function.fixedPoints u.val.val := fun x hx => hx u
  apply Set.eq_of_subset_of_ncard_le hsub
  rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hfixed,
    Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,u.val.val.sum_cycleType,hcard,hsupp]

private theorem free_off_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q)
    (hfixed : Nat.card (fixedPoints Q X) = 6)
    (h9 : 9 ∣ Nat.card (Subgroup.centralizer (Q : Set P))) :
    ∀ q : Q, ∀ x : X, x ∉ fixedPoints Q X → q • x = x → q = 1 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro q x hx hqx
  by_contra hq
  let R : Subgroup Q := stabilizer Q x
  have hRne : R ≠ ⊥ := by
    intro he
    have hmem : q ∈ R := hqx
    rw [he,Subgroup.mem_bot] at hmem
    exact hq hmem
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup R)
  have hepos : 1 ≤ e := by
    by_contra hn
    have hc : Nat.card R = 1 := by rw [he,show e = 0 by omega,pow_zero]
    exact hRne (Subgroup.card_eq_one.mp hc)
  have hp : 5 ∣ Nat.card R := by rw [he]; exact pow_dvd_pow 5 hepos
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := R) 5 hp
  have huQ : orderOf u.val = 5 := (Subgroup.orderOf_coe u).trans hu
  have hfixeq := order_five_fixedPoints_eq P hcard h5 hnotAlt Q hfixed h9 u.val huQ
  apply hx
  rw [hfixeq]
  exact u.property

theorem card_eq_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q) (hQne : Q ≠ ⊥)
    (hfixed : Nat.card (fixedPoints Q X) = 6)
    (h9 : 9 ∣ Nat.card (Subgroup.centralizer (Q : Set P))) : Nat.card Q = 5 := by
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hd := FreeComplementCard.card_dvd_complement Q X (fixedPoints Q X)
    (fun q x hx => by simpa only [hx q] using hx)
    (free_off_fixed P hcard h5 hnotAlt Q hQ hfixed h9)
  rw [Nat.card_eq_fintype_card (α := X),hcard,← Nat.card_coe_set_eq,hfixed] at hd
  change Nat.card Q ∣ 30 at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have hele : e ≤ 1 := by
    by_contra hn
    have h25 : 25 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 5 (by omega : 2 ≤ e)
    have hh := h25.trans hd
    norm_num at hh
  have hene : e ≠ 0 := by
    intro he0
    apply hQne
    apply Subgroup.card_eq_one.mp
    rw [he,he0,pow_zero]
  have he1 : e = 1 := by omega
  simpa only [he1,pow_one] using he

end FiveTransitive.Degree36FiveCentralizerSemiregular

end CFSG
