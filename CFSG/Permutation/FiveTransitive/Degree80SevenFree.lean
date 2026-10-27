module

public import CFSG.Permutation.FiveTransitive.Degree80PrimeFixedBound
public import CFSG.Permutation.FiveTransitive.Degree80SevenSingleFiveLift
public import CFSG.Permutation.FiveTransitive.SevenOrbitLocalFixedCount

public section

namespace CFSG

namespace FiveTransitive.Degree80SevenFree
open MulAction SylowFixedActionCore

private theorem sylow_card_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 7 (fixingSubgroup P s)) : Nat.card S = 1 := by
  by_contra hS
  obtain ⟨g,hg,hlocal,hlabels⟩ :=
    Degree80SevenSingleFiveLift.exists_five_with_fixed_five P hcard h5 hnotAlt s hs S hS
  let Q := sylowImage X P s S
  have hQ : IsPGroup 7 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hcount := SevenOrbitLocalFixedCount.local_add_seven_mul_fixed_labels_le
    P Q hQ g (hg ▸ pow_orderOf_eq_one g)
  rw [hlocal,hlabels] at hcount
  have hb := Degree80PrimeFixedBound.five_fixed_card_le P hcard h5 hnotAlt g.val
    ((Subgroup.orderOf_coe g).trans hg)
  omega

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 7 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hd
  let S : Sylow 7 (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : 7 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  rw [sylow_card_eq_one P hcard h5 hnotAlt s hs S] at hdiv
  norm_num at hdiv

theorem fixed_card_eq_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 7) : Nat.card (Function.fixedPoints g.val) = 3 := by
  classical
  have hlt : Nat.card (Function.fixedPoints g.val) < 5 := by
    by_contra hn
    have hf : 5 ≤ (Function.fixedPoints g.val).ncard := by rw [←Nat.card_coe_set_eq]; omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hf
    let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
    have hu : orderOf u = 7 := (Subgroup.orderOf_coe u).symm.trans hg
    exact not_dvd_five_fixer P hcard h5 hnotAlt s hs (hu ▸ orderOf_dvd_natCard u)
  have hgperm : orderOf g.val = 7 := (Subgroup.orderOf_coe g).trans hg
  obtain ⟨m,hm⟩ := Equiv.Perm.cycleType_prime_order (σ := g.val) (by rw [hgperm]; norm_num)
  have hsum := g.val.sum_cycleType
  rw [hm,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hgperm] at hsum
  have hle : g.val.support.card ≤ 80 := hcard ▸ Finset.card_le_univ g.val.support
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.val.sum_cycleType,hcard] at hlt ⊢
  omega

end FiveTransitive.Degree80SevenFree

end CFSG
