module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.FullFixerFixedAction

open MulAction FixedNormalizerAction
open scoped Pointwise

private theorem fixing_eq_of_range_subset
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    {k : ℕ} (hk : IsMultiplyPretransitive G X k)
    (s : Set X) (hs : s.ncard = k) (e : Fin k ↪ X)
    (he : Set.range e ⊆ fixedPoints (fixingSubgroup G s) X) :
    fixingSubgroup G (Set.range e) = fixingSubgroup G s := by
  have ht : (Set.range e).ncard = k := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective e.injective
  have hs' : IsMultiplyPretransitive G X s.ncard := by simpa only [hs] using hk
  have ht' : IsMultiplyPretransitive G X (Set.range e).ncard := by simpa only [ht] using hk
  have hi : (fixingSubgroup G s).index = (fixingSubgroup G (Set.range e)).index := by
    rw [hs'.index_of_fixingSubgroup_eq s,ht'.index_of_fixingSubgroup_eq (Set.range e),hs,ht]
  have hc : Nat.card (fixingSubgroup G s) = Nat.card (fixingSubgroup G (Set.range e)) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := fixingSubgroup G s)))
    rw [(fixingSubgroup G s).index_mul_card,hi,(fixingSubgroup G (Set.range e)).index_mul_card]
  apply (Subgroup.eq_of_le_of_card_ge ?_ (by omega : Nat.card (fixingSubgroup G (Set.range e)) ≤ Nat.card (fixingSubgroup G s))).symm
  intro g hg
  apply (mem_fixingSubgroup_iff G).mpr
  intro x hx
  exact mem_fixedPoints.mp (he hx) ⟨g,hg⟩

theorem normalizer_multiply
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    {k : ℕ} (hk : IsMultiplyPretransitive G X k)
    (s : Set X) (hs : s.ncard = k) :
    IsMultiplyPretransitive (Normalizer (fixingSubgroup G s))
      (Fixed (X := X) (fixingSubgroup G s)) k := by
  rw [isMultiplyPretransitive_iff]
  intro a b
  let H := fixingSubgroup G s
  let aX := ambientEmbedding a
  let bX := ambientEmbedding b
  have hf (c : Fin k ↪ Fixed (X := X) H) :
      fixingSubgroup G (Set.range (ambientEmbedding c)) = H := by
    apply fixing_eq_of_range_subset hk s hs
    rintro x ⟨i,rfl⟩
    exact (fixed_eq (X := X) H) ▸ (c i).property
  obtain ⟨g,hg⟩ := hk.exists_smul_eq aX bX
  have hrange : g • Set.range aX = Set.range bX := by
    ext x
    constructor
    · rintro ⟨y,⟨i,rfl⟩,rfl⟩
      exact ⟨i,(DFunLike.congr_fun hg i).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨aX i,⟨i,rfl⟩,DFunLike.congr_fun hg i⟩
  have hgn : g ∈ Normalizer H := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have h := SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj (Set.range aX) g
    rw [hrange,hf a,hf b] at h
    exact h.symm
  refine ⟨⟨g,hgn⟩,?_⟩
  ext i
  exact congrArg Subtype.val (Subtype.ext (DFunLike.congr_fun hg i) :
    (⟨g,hgn⟩ : Normalizer H) • a i = b i)

theorem image_base_fixer_eq_bot
    {G X : Type*} [Group G] [MulAction G X] (s : Set X) :
    fixingSubgroup (Image (X := X) (fixingSubgroup G s))
      {x : Fixed (X := X) (fixingSubgroup G s) | (x : X) ∈ s} = ⊥ := by
  let H := fixingSubgroup G s
  let F := Fixed (X := X) H
  let J := Image (X := X) H
  have hsF : s ⊆ (F : Set X) := by
    change s ⊆ Fixed (X := X) H
    rw [fixed_eq]
    intro x hx h
    exact (mem_fixingSubgroup_iff G).mp h.property x hx
  rw [Subgroup.eq_bot_iff_forall]
  intro j hj
  obtain ⟨g,hg⟩ := j.property
  have hgH : (g : G) ∈ H := by
    apply (mem_fixingSubgroup_iff G).mpr
    intro x hx
    have h := (mem_fixingSubgroup_iff J).mp hj ⟨x,hsF hx⟩ hx
    change j.val ⟨x,hsF hx⟩ = ⟨x,hsF hx⟩ at h
    rw [← hg] at h
    exact congrArg Subtype.val h
  apply Subtype.ext
  rw [← hg]
  apply Equiv.ext
  intro x
  apply Subtype.ext
  have hx : x.val ∈ fixedPoints H X := by
    rw [← fixed_eq H]
    exact x.property
  exact mem_fixedPoints.mp hx ⟨g.val,hgH⟩

end FiveTransitive.FullFixerFixedAction

end CFSG
