module

public import CFSG.Permutation.FiveTransitive.Degree36LargePrimeFree
public import CFSG.Permutation.FiveTransitive.AmbientSylowSmallFixedImage

public section

namespace CFSG

namespace FiveTransitive.Degree36LargeSylowEntrance

open MulAction Subgroup FixedNormalizerAction

theorem factorization_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 17 ∨ p = 11) : (Nat.card P).factorization p = 1 := by
  classical
  let _ := h5
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi] at hm
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hn := Degree36LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hprime
    (by rcases hp with rfl | rfl <;> omega)
  rw [← hm,Nat.factorization_mul (by norm_num) Nat.card_pos.ne',Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hn,add_zero]
  rcases hp with rfl | rfl
  · rw [show 45239040 = 17 * 2661120 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),Finsupp.add_apply,
      (show Nat.Prime 17 by norm_num).factorization,Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),add_zero]
  · rw [show 45239040 = 11 * 4112640 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),Finsupp.add_apply,
      (show Nat.Prime 11 by norm_num).factorization,Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),add_zero]

theorem sylow_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 17 ∨ p = 11) (S : Sylow p P) : Nat.card S = p := by
  let _ : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  rw [S.card_eq_multiplicity,factorization_eq_one P hcard h5 hnotAlt hp,pow_one]

private theorem element_fixed_lt_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 17 ∨ p = 11) (u : P) (hu : orderOf u = p) :
    Nat.card (Function.fixedPoints u.val) < 5 := by
  classical
  by_contra hn
  have hlarge : 5 ≤ (Function.fixedPoints u.val).ncard := by
    rw [← Nat.card_coe_set_eq]; omega
  obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hlarge
  let v : fixingSubgroup P s := ⟨u,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
  have hv : orderOf v = p := by rw [← Subgroup.orderOf_coe v]; exact hu
  have hd : p ∣ Nat.card (fixingSubgroup P s) := hv ▸ orderOf_dvd_natCard v
  exact Degree36LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p
    (by rcases hp with rfl | rfl <;> norm_num)
    (by rcases hp with rfl | rfl <;> omega) hd

theorem element_cycle_type
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 17 ∨ p = 11) (u : P) (hu : orderOf u = p) :
    u.val.cycleType = Multiset.replicate (36 / p) p := by
  have hg : orderOf u.val = p := (Subgroup.orderOf_coe u).trans hu
  obtain ⟨k,hk⟩ := Equiv.Perm.cycleType_prime_order (σ := u.val)
    (by rw [hg]; rcases hp with rfl | rfl <;> norm_num)
  have hsum := u.val.sum_cycleType
  rw [hk,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hg] at hsum
  have hle : u.val.support.card ≤ 36 := hcard ▸ Finset.card_le_univ u.val.support
  have hfix := element_fixed_lt_five P hcard h5 hnotAlt hp u hu
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,u.val.sum_cycleType,hcard] at hfix
  have he : k + 1 = 36 / p := by rcases hp with rfl | rfl <;> omega
  rw [hk,hg,he]

theorem fixed_and_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 17 ∨ p = 11) (S : Sylow p P) :
    Nat.card (fixedPoints S X) = 36 % p ∧ Image (X := X) (S : Subgroup P) = ⊤ := by
  classical
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  let _ : Fact p.Prime := ⟨hprime⟩
  have hS := sylow_card P hcard h5 hnotAlt hp S
  let _ : IsCyclic S := isCyclic_of_prime_card hS
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huP : orderOf u.val = p := (Subgroup.orderOf_coe u).trans (hu.trans hS)
  have hsub : fixedPoints S X ⊆ Function.fixedPoints u.val.val := fun x hx => hx u
  have hle := Set.ncard_le_ncard hsub
  rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq] at hle
  have hfix := element_fixed_lt_five P hcard h5 hnotAlt hp u.val huP
  have hm := S.isPGroup'.card_modEq_card_fixedPoints X
  change Nat.card X % p = Nat.card (fixedPoints S X) % p at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  have hfixed : Nat.card (fixedPoints S X) = 36 % p := by
    rcases hp with rfl | rfl <;> omega
  exact ⟨hfixed,AmbientSylowSmallFixedImage.sylow_fixed_image p (36 % p) hprime
    (by rcases hp with rfl | rfl <;> norm_num) P (by omega) h5 S hfixed⟩

end FiveTransitive.Degree36LargeSylowEntrance

end CFSG
