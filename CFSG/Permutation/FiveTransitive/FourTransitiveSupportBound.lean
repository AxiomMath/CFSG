module

public import CFSG.Permutation.FiveTransitive.FourTransitiveSupportArithmetic
public import CFSG.Permutation.FiveTransitive.FamilyCommutatorAverage
public import CFSG.Permutation.FiveTransitive.RefinedCommutatorMinimalSupport
public import CFSG.Permutation.FiveTransitive.FourTransitiveConjugateCounts

public section

namespace CFSG

namespace FiveTransitive.FourTransitiveSupportBound

open Equiv

private theorem exists_conjugate_fixing_moving
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h2 : MulAction.IsMultiplyPretransitive P X 2)
    (g : Perm X) (hg : g ∈ P) (hmpos : 0 < g.support.card)
    (hmproper : g.support.card < Fintype.card X)
    {α β : X} (hαβ : α ≠ β) :
    ∃ v : Perm X, v ∈ P ∧ v.support.card = g.support.card ∧
      v α = α ∧ v β ≠ β := by
  classical
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hmpos
  obtain ⟨a, ha⟩ : ∃ a, a ∉ g.support := by
    by_contra h
    push Not at h
    have huniv := Finset.eq_univ_of_forall h
    simp only [huniv, Finset.card_univ, lt_self_iff_false] at hmproper
  have hab : a ≠ b := by intro heq; exact ha (heq ▸ hb)
  obtain ⟨h, hha, hhb⟩ := MulAction.is_two_pretransitive_iff.mp h2 hab hαβ
  let v : Perm X := (h : Perm X) * g * (h : Perm X)⁻¹
  have hiα : (h : Perm X)⁻¹ α = a := by
    rw [← hha]
    exact (h : Perm X).symm_apply_apply a
  have hiβ : (h : Perm X)⁻¹ β = b := by
    rw [← hhb]
    exact (h : Perm X).symm_apply_apply b
  have hga : g a = a := by simpa only [Perm.mem_support, not_not] using ha
  refine ⟨v, P.mul_mem (P.mul_mem h.property hg) (P.inv_mem h.property), ?_, ?_, ?_⟩
  · simp only [v, Perm.support_conj, Finset.card_map]
  · simp only [v, Perm.mul_apply, hiα, hga]
    exact hha
  · intro heq
    change (h : Perm X) (g ((h : Perm X)⁻¹ β)) = β at heq
    rw [hiβ] at heq
    have hgb : g b = b := (h : Perm X).injective (heq.trans hhb.symm)
    exact (Perm.mem_support.mp hb) hgb

theorem bound_of_four_transitive
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h4 : MulAction.IsMultiplyPretransitive P X 4)
    (g : Perm X) (hg : g ∈ P)
    (hminimal : ∀ u : Perm X, u ∈ P → u ≠ 1 → g.support.card ≤ u.support.card)
    (hm : 9 ≤ g.support.card) : Fintype.card X ≤ 2 * g.support.card + 3 := by
  classical
  have hmn : g.support.card ≤ Fintype.card X := Finset.card_le_univ _
  by_cases heq : g.support.card = Fintype.card X
  · omega
  have hlt : g.support.card < Fintype.card X := by omega
  obtain ⟨α, hα⟩ := Finset.card_pos.mp (show 0 < g.support.card by omega)
  have hαβ : α ≠ g α := Ne.symm (Perm.mem_support.mp hα)
  let _ : MulAction.IsMultiplyPretransitive P X 4 := h4
  have h2 : MulAction.IsMultiplyPretransitive P X 2 :=
    MulAction.isMultiplyPretransitive_of_le (G := P) (α := X) (m := 2) (n := 4)
      (by omega) (by simpa only [Nat.card_eq_fintype_card] using (show 4 ≤ Fintype.card X by omega))
  obtain ⟨v, hvP, hvm, hvα, hvβ⟩ :=
    exists_conjugate_fixing_moving P h2 g hg (by omega) hlt hαβ
  let K := FourTransitiveConjugateCounts.twoPointFixer P α (g α)
  let _ : Fintype K := Fintype.ofFinite K
  let fam : K → Perm X := FourTransitiveConjugateCounts.conjugate v
  have hki (k : K) (x : X) (hx : x ∈ ({α, g α} : Set X)) :
      (k.val : Perm X).symm x = x :=
    (mem_fixingSubgroup_iff P).mp (k⁻¹).property x hx
  have hfix (k : K) : fam k α = α := by
    apply (FourTransitiveConjugateCounts.conjugate_apply_eq_iff v k α α).mpr
    rw [hki k α (by simp)]
    exact hvα
  have hmove (k : K) : fam k (g α) ≠ g α := by
    intro heq
    have he := (FourTransitiveConjugateCounts.conjugate_apply_eq_iff v k (g α) (g α)).mp heq
    rw [hki k (g α) (by simp)] at he
    exact hvβ he
  have hmem (k : K) : fam k ∈ P :=
    P.mul_mem (P.mul_mem k.val.property hvP) (P.inv_mem k.val.property)
  apply FourTransitiveSupportArithmetic.degree_bound _ _ hm
  apply FamilyCommutatorAverage.refined_sum_inequality g α hα fam hfix hmove
  · intro γ hγα hγβ
    simpa only [hvm] using
      FourTransitiveConjugateCounts.card_moved P h4 v hαβ hvα hvβ hγα hγβ
  · intro γ hγα hγβ
    exact FourTransitiveConjugateCounts.card_maps_right P h4 v hαβ hvα hvβ hγα hγβ
  · intro γ δ hγα hγβ hδα hδβ hγδ
    simpa only [hvm] using
      FourTransitiveConjugateCounts.card_maps_other P h4 v hαβ hvα hvβ hγα hγβ hδα hδβ hγδ
  · intro γ δ hγα hγβ hδα hδβ hγδ
    simpa only [hvm] using
      FourTransitiveConjugateCounts.card_fixed_moved P h4 v hαβ hvα hvβ hγα hγβ hδα hδβ hγδ
  · intro k
    exact RefinedCommutatorMinimalSupport.bound_of_fixed_moved_image
      P g (fam k) hg (hmem k) hminimal α (hfix k) (hmove k)

end FiveTransitive.FourTransitiveSupportBound

end CFSG
