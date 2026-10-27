module

public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan

public section

namespace CFSG

namespace FiveTransitive.Degree28LargePrimeThirteen

open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Finset X) (hs : s.card = 5) (p : ℕ) (hp : p.Prime) (hlarge : 13 ≤ p) :
    ¬ p ∣ Nat.card (fixingSubgroup P (s : Set X)) := by
  intro hd
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' p hd
  let g : Equiv.Perm X := (u : P)
  have hg : orderOf g = p := (Subgroup.orderOf_coe (u : P)).trans
    ((Subgroup.orderOf_coe u).trans hu)
  have hsupport : g.support.card ≤ 23 := by
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

end FiveTransitive.Degree28LargePrimeThirteen

end CFSG
