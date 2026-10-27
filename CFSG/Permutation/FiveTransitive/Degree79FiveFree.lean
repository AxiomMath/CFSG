module

public import CFSG.Permutation.FiveTransitive.Degree79SevenFree

public section

namespace CFSG

namespace FiveTransitive.Degree79FiveFree
open MulAction SylowFixedActionCore

private theorem sylow_card_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 5 (fixingSubgroup P s)) : Nat.card S = 1 := by
  by_contra hS
  obtain ⟨g,hg,hlarge⟩ := Degree79FiveLargeSeven.exists_normalizer_seven P hcard h5 hnotAlt s hs S hS
  have hfix := Degree79SevenFree.fixed_card_eq_two P hcard h5 hnotAlt g.val
    ((Subgroup.orderOf_coe g).trans hg)
  omega

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 5 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hd
  let S : Sylow 5 (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : 5 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  rw [sylow_card_eq_one P hcard h5 hnotAlt s hs S] at hdiv
  norm_num at hdiv

theorem fixed_card_eq_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) : Nat.card (Function.fixedPoints g.val) = 4 := by
  classical
  have hlt : Nat.card (Function.fixedPoints g.val) < 5 := by
    by_contra hn
    have hf : 5 ≤ (Function.fixedPoints g.val).ncard := by rw [← Nat.card_coe_set_eq]; omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hf
    let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
    have hu : orderOf u = 5 := (Subgroup.orderOf_coe u).symm.trans hg
    exact not_dvd_five_fixer P hcard h5 hnotAlt s hs (hu ▸ orderOf_dvd_natCard u)
  have hcases := Degree79FiveSharpGlobal.fixed_card_cases P hcard h5 hnotAlt g hg
  omega

end FiveTransitive.Degree79FiveFree

end CFSG
