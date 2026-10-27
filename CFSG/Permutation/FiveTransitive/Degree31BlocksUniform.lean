module

public import CFSG.Permutation.FiveTransitive.Degree31BlocksDefinition
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

public section

namespace CFSG

namespace FiveTransitive.Degree31Blocks

open MulAction
open scoped Pointwise

private theorem fixingSubgroup_card_smul
    {G X : Type} [Group G] [MulAction G X] (g : G) (s : Set X) :
    Nat.card (fixingSubgroup G (g • s)) = Nat.card (fixingSubgroup G s) :=
  (Nat.card_congr (SubMulAction.fixingSubgroupEquivFixingSubgroup
    (M := G) (g := g) (t := s) rfl).toEquiv).symm

private theorem smul_mem_blocks
    {X : Type} [DecidableEq X] (P : Subgroup (Equiv.Perm X))
    (g : P) (b : Finset X) (hb : b ∈ blocks P) : g • b ∈ blocks P := by
  change (g • b).card = 7 ∧ Nat.card (fixingSubgroup P ((g • b : Finset X) : Set X)) = 2048
  constructor
  · simpa only [Finset.card_smul_finset] using hb.1
  · rw [Finset.coe_smul_finset,fixingSubgroup_card_smul]
    exact hb.2

private def familyThroughEquiv
    {G X : Type} [Group G] [MulAction G X] [DecidableEq X]
    (B : Set (Finset X)) (hB : ∀ g : G, ∀ b ∈ B, g • b ∈ B)
    (g : G) (s : Set X) :
    {b : Finset X // b ∈ B ∧ s ⊆ (b : Set X)} ≃
      {b : Finset X // b ∈ B ∧ g • s ⊆ (b : Set X)} where
  toFun b := ⟨g • b.val,hB g b.val b.prop.1,by
    rw [Finset.coe_smul_finset]
    exact Set.smul_set_subset_smul_set_iff.mpr b.prop.2⟩
  invFun b := ⟨g⁻¹ • b.val,hB g⁻¹ b.val b.prop.1,by
    rw [Finset.coe_smul_finset]
    have h := (Set.smul_set_subset_smul_set_iff (a := g⁻¹)).mpr b.prop.2
    simpa only [inv_smul_smul] using h⟩
  left_inv b := Subtype.ext (inv_smul_smul g b.val)
  right_inv b := Subtype.ext (smul_inv_smul g b.val)

private theorem exists_smul_eq_five_sets
    {G X : Type} [Group G] [MulAction G X] [Fintype X] [DecidableEq X]
    (h5 : IsMultiplyPretransitive G X 5)
    (s t : Set X) (hs : s.ncard = 5) (ht : t.ncard = 5) : ∃ g : G, g • s = t := by
  classical
  let _ : IsPretransitive G (Set.powersetCard X 5) :=
    Set.powersetCard.isPretransitive_of_isMultiplyPretransitive G h5
  let sf := s.toFinite.toFinset
  let tf := t.toFinite.toFinset
  have hsf : sf.card = 5 := by rw [← Set.ncard_coe_finset,s.toFinite.coe_toFinset]; exact hs
  have htf : tf.card = 5 := by rw [← Set.ncard_coe_finset,t.toFinite.coe_toFinset]; exact ht
  let s' : Set.powersetCard X 5 := Set.powersetCard.ofCard hsf
  let t' : Set.powersetCard X 5 := Set.powersetCard.ofCard htf
  obtain ⟨g,hg⟩ := exists_smul_eq G s' t'
  have he : g • sf = tf := congrArg Subtype.val hg
  have he' := congrArg (fun b : Finset X => (b : Set X)) he
  rw [Finset.coe_smul_finset] at he'
  exact ⟨g,by simpa only [sf,tf,Set.Finite.coe_toFinset] using he'⟩

private theorem card_blocksThrough_eq
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (h5 : IsMultiplyPretransitive P X 5)
    (s t : Set X) (hs : s.ncard = 5) (ht : t.ncard = 5) :
    Nat.card (blocksThrough P s) = Nat.card (blocksThrough P t) := by
  obtain ⟨g,rfl⟩ := exists_smul_eq_five_sets h5 s t hs ht
  exact Nat.card_congr (familyThroughEquiv (blocks P) (smul_mem_blocks P) g s)

private theorem card_filter_blockFinset
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (s : Set X) [DecidablePred (fun b : Finset X => s ⊆ (b : Set X))] :
    ((blockFinset P).filter (fun b : Finset X => s ⊆ (b : Set X))).card = Nat.card (blocksThrough P s) := by
  classical
  let e : ↥((blockFinset P).filter (fun b : Finset X => s ⊆ (b : Set X))) ≃ blocksThrough P s :=
    Equiv.subtypeEquivRight (fun b => by simp)
  calc
    ((blockFinset P).filter (fun b : Finset X => s ⊆ (b : Set X))).card =
        Nat.card ↥((blockFinset P).filter (fun b : Finset X => s ⊆ (b : Set X))) := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ = Nat.card (blocksThrough P s) := Nat.card_congr e

theorem card_filter_eq_of_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (h5 : IsMultiplyPretransitive P X 5)
    (s t : Finset X) (hs : s.card = 5) (ht : t.card = 5) :
    ((blockFinset P).filter (fun b => s ⊆ b)).card =
      ((blockFinset P).filter (fun b => t ⊆ b)).card := by
  classical
  have hs' : (s : Set X).ncard = 5 := by simpa using hs
  have ht' : (t : Set X).ncard = 5 := by simpa using ht
  have he := card_blocksThrough_eq P h5 (s : Set X) (t : Set X) hs' ht'
  rw [← card_filter_blockFinset P (s : Set X), ← card_filter_blockFinset P (t : Set X)] at he
  simpa only [Finset.coe_subset] using he

end FiveTransitive.Degree31Blocks

end CFSG
