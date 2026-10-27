module

public import CFSG.Permutation.FiveTransitive.Degree36SmallPrimesFree

public section

namespace CFSG

namespace FiveTransitive.Degree36LargePrimeFree

open MulAction

private theorem long_not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Finset X) (hs : s.card = 5) (p : ℕ) (hp : p.Prime) (hlarge : 17 ≤ p) :
    ¬ p ∣ Nat.card (fixingSubgroup P (s : Set X)) := by
  intro hd
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' p hd
  let g : Equiv.Perm X := (u : P)
  have hg : orderOf g = p := (Subgroup.orderOf_coe (u : P)).trans
    ((Subgroup.orderOf_coe u).trans hu)
  have hsupport : g.support.card ≤ 31 := by
    have hsub : g.support ⊆ sᶜ := by
      intro x hx
      apply Finset.mem_compl.mpr
      intro hxs
      exact (Equiv.Perm.mem_support.mp hx)
        ((mem_fixingSubgroup_iff P).mp u.property x hxs)
    have h := Finset.card_le_card hsub
    rw [Finset.card_compl,hcard,hs] at h
    exact h
  have hcycle : g.IsCycle := Equiv.Perm.isCycle_of_prime_order (by rwa [hg]) (by rw [hg]; omega)
  have hsupp : g.support.card = p := by rw [← hcycle.orderOf,hg]
  have h2 : IsMultiplyPretransitive P X 2 := by
    let _ := h5
    exact isMultiplyPretransitive_of_le (G := P) (α := X) (n := 5) (by omega) (by rw [Nat.card_eq_fintype_card,hcard]; omega)
  have hprim := isPreprimitive_of_is_two_pretransitive h2
  apply hnotAlt
  apply OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    hprim hp (by rw [Nat.card_eq_fintype_card,hcard]; omega) hcycle hsupp
  exact (u : P).property

private theorem not_dvd_five_fixer_finset
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Finset X) (hs : s.card = 5) (p : ℕ) (hp : p.Prime) (hlarge : 7 ≤ p) :
    ¬ p ∣ Nat.card (fixingSubgroup P (s : Set X)) := by
  by_cases hsmall : p = 7 ∨ p = 11 ∨ p = 13
  · exact Degree36SmallPrimesFree.not_dvd_five_fixer p hp hsmall P hcard h5 hnotAlt
      (s : Set X) (by simpa only [Set.ncard_coe_finset] using hs)
  · have h17 : 17 ≤ p := by
      by_contra hn
      have hupper : p ≤ 16 := by omega
      interval_cases p <;> norm_num at *
    exact long_not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp h17

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (p : ℕ) (hp : p.Prime) (hlarge : 7 ≤ p) :
    ¬ p ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let sf := s.toFinite.toFinset
  have he : (sf : Set X) = s := s.toFinite.coe_toFinset
  have hsf : sf.card = 5 := by rw [← Set.ncard_coe_finset,he]; exact hs
  have hn := not_dvd_five_fixer_finset P hcard h5 hnotAlt sf hsf p hp hlarge
  rwa [he] at hn

end FiveTransitive.Degree36LargePrimeFree

end CFSG
