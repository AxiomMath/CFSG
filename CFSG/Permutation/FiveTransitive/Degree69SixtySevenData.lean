module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum.Prime
public import CFSG.Permutation.FiveTransitive.MinimalOrbitStabilizer

public section

namespace CFSG

namespace FiveTransitive.Degree69SixtySevenData
open MulAction Subgroup

private theorem factorization_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ 67 ∣ Nat.card (fixingSubgroup P s)) : (Nat.card P).factorization 67 = 1 := by
  classical
  let _ := h5
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi] at hm
  have hn := hfree s hs
  rw [← hm,Nat.factorization_mul (by norm_num) Nat.card_pos.ne',Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hn,add_zero]
  rw [show 1348621560 = 67 * 20128680 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num),Finsupp.add_apply,
    (show Nat.Prime 67 by norm_num).factorization,Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num),add_zero]

theorem sylow_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ 67 ∣ Nat.card (fixingSubgroup P s))
    (S : Sylow 67 P) : Nat.card S = 67 := by
  let _ : Fact (Nat.Prime 67) := ⟨by norm_num⟩
  rw [S.card_eq_multiplicity,factorization_eq_one P hcard h5 hfree,pow_one]

theorem fixed_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hn : Fintype.card X = 69)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ 67 ∣ Nat.card (fixingSubgroup P s))
    (Q : Subgroup P) (hQ : IsPGroup 67 Q) (hne : Q ≠ ⊥) :
    Nat.card (fixedPoints Q X) = 2 := by
  classical
  let _ : Fact (Nat.Prime 67) := ⟨by norm_num⟩
  have hpd : 67 ∣ Nat.card Q := hQ.card_eq_or_dvd.resolve_left (by
    intro he; exact hne (Subgroup.card_eq_one.mp he))
  have hlt : Nat.card (fixedPoints Q X) < 5 := by
    by_contra hh
    have hlarge : 5 ≤ (fixedPoints Q X).ncard := by rw [← Nat.card_coe_set_eq]; omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hlarge
    let i : Q →* fixingSubgroup P s := Q.subtype.codRestrict (fixingSubgroup P s)
      (fun q => (mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx q))
    have hi : Function.Injective i := by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : fixingSubgroup P s => z.val) hab)
    exact hfree s hs (hpd.trans (Subgroup.card_dvd_of_injective i hi))
  have hm := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % 67 = Nat.card (fixedPoints Q X) % 67 at hm
  rw [Nat.card_eq_fintype_card (α := X),hn] at hm
  have he : (69 : ℕ) % 67 = 2 := by norm_num
  rw [he,Nat.mod_eq_of_lt (by omega : Nat.card (fixedPoints Q X) < 67)] at hm
  exact hm.symm

end FiveTransitive.Degree69SixtySevenData

end CFSG
