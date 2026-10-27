module

public import CFSG.Permutation.FiveTransitive.EvenSixInvolution
public import CFSG.Permutation.FiveTransitive.SimpleIndexBound
public import CFSG.Permutation.FiveTransitive.A6OrderArithmetic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.TwoTransitiveA6Card

open Equiv MulAction

theorem two_fixer_index
    {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (H : Subgroup (Perm X)) (h2 : IsMultiplyPretransitive H X 2)
    (s : Set X) (hs : s.ncard = 2) : (fixingSubgroup H s).index = 30 := by
  have h := h2.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hX] at h
  norm_num [Nat.factorial] at h
  omega

private theorem card_ne_thirty
    {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (H : Subgroup (Perm X)) (hH : H ≤ alternatingGroup X)
    (h2 : IsMultiplyPretransitive H X 2) : Nat.card H ≠ 30 := by
  classical
  intro hcard
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 (by rw [hcard]; decide)
  have hgorder : orderOf (g : Perm X) = 2 :=
    (orderOf_injective H.subtype H.subtype_injective g).trans hg
  have hgpow : (g : Perm X) ^ 2 = 1 := by
    rw [← hgorder]
    exact pow_orderOf_eq_one _
  have hsign : (g : Perm X).sign = 1 := Perm.mem_alternatingGroup.mp (hH g.property)
  have hf := EvenSixInvolution.two_le_fixed_card hX (g : Perm X) hgpow hsign
  let F := Function.fixedPoints (g : Perm X)
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (Function.fixedPoints (g : Perm X))
    omega)
  obtain ⟨a,b,hab⟩ := exists_pair_ne F
  have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  let s : Set X := {a.val,b.val}
  have hs : s.ncard = 2 := by simp [s,hab']
  have hi := two_fixer_index hX H h2 s hs
  have hmul := (fixingSubgroup H s).index_mul_card
  rw [hi,hcard] at hmul
  have hbot : fixingSubgroup H s = ⊥ := Subgroup.card_eq_one.mp (by omega)
  have hgfix : g ∈ fixingSubgroup H s := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    rcases hx with rfl | rfl
    · exact a.property
    · exact b.property
  have hgone : g = 1 := by simpa only [hbot, Subgroup.mem_bot] using hgfix
  rw [hgone, orderOf_one] at hg
  omega

theorem card_eq_sixty_or_three_hundred_sixty
    {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (H : Subgroup (Perm X)) (hH : H ≤ alternatingGroup X)
    (h2 : IsMultiplyPretransitive H X 2) :
    Nat.card H = 60 ∨ Nat.card H = 360 := by
  classical
  let A := alternatingGroup X
  let K : Subgroup A := H.subgroupOf A
  let _ : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hAcard : Nat.card A = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, hX]
    norm_num [Nat.factorial]
  have hKcard : Nat.card K = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have hprod := K.index_mul_card
  rw [hAcard,hKcard] at hprod
  have hd : Nat.card H ∣ 360 := by
    rw [← hAcard, ← hKcard]
    exact Subgroup.card_subgroup_dvd_card K
  have hle : Nat.card H ≤ 360 := Nat.le_of_dvd (by decide) hd
  have h30 : 30 ∣ Nat.card H := by
    obtain ⟨e⟩ : Nonempty (Fin 2 ↪ X) := Function.Embedding.nonempty_of_card_le (by simp [hX])
    have hs : (Set.range e).ncard = 2 := by simp [Set.ncard_range_of_injective e.injective]
    have hi := two_fixer_index hX H h2 (Set.range e) hs
    have hmul := (fixingSubgroup H (Set.range e)).index_mul_card
    rw [hi] at hmul
    exact ⟨_,hmul.symm⟩
  have hneq := card_ne_thirty hX H hH h2
  by_cases htop : K = ⊤
  · right
    rw [← hKcard, htop, Subgroup.card_top, hAcard]
  have hsimple : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by
    rw [Nat.card_eq_fintype_card,hX]
    decide)
  let _ := hsimple
  have hbound := SimpleIndexBound.card_le_factorial_index A K htop
  rw [hAcard] at hbound
  exact A6OrderArithmetic.sixty_or_full (Nat.card H) K.index h30 hle hneq hprod hbound

end FiveTransitive.TwoTransitiveA6Card

end CFSG
