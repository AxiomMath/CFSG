module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin

open Equiv G6

namespace GE23

@[expose] def sa : Perm (Fin 5) := swap 0 1

@[expose] def sb : Perm (Fin 5) := swap 2 3

@[expose] def sr : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def d8 : Subgroup (Perm (Fin 5)) := Subgroup.closure {sa, sb, sr}

@[expose] def e4 : Subgroup (Perm (Fin 5)) := Subgroup.closure {sa, sb}

@[expose] def d8list : List (Perm (Fin 5)) :=
  [1, sa, sb, sa * sb, sr, sr * sa, sr * sb, sr * sa * sb]

@[expose] def e4list : List (Perm (Fin 5)) := [1, sa, sb, sa * sb]

theorem mem_e4_iff {x : Perm (Fin 5)} : x ∈ e4 ↔ x ∈ e4list := by
  have hcl : ∀ y ∈ e4list, ∀ z ∈ e4list, y * z ∈ e4list := by decide +kernel
  have hinv : ∀ y ∈ e4list, y⁻¹ ∈ e4list := by decide +kernel
  constructor
  · intro hx
    refine Subgroup.closure_induction (p := fun x _ => x ∈ e4list) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with rfl | rfl
      · decide +kernel
      · decide +kernel
    · decide +kernel
    · intro y z _ _ hy hz
      exact hcl y hy z hz
    · intro y _ hy
      exact hinv y hy
  · intro hx
    have hsa : sa ∈ e4 := Subgroup.subset_closure (Or.inl rfl)
    have hsb : sb ∈ e4 := Subgroup.subset_closure (Or.inr rfl)
    simp only [e4list, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact e4.one_mem
    · exact hsa
    · exact hsb
    · exact e4.mul_mem hsa hsb

theorem mem_d8_iff {x : Perm (Fin 5)} : x ∈ d8 ↔ x ∈ d8list := by
  have hcl : ∀ y ∈ d8list, ∀ z ∈ d8list, y * z ∈ d8list := by decide +kernel
  have hinv : ∀ y ∈ d8list, y⁻¹ ∈ d8list := by decide +kernel
  constructor
  · intro hx
    refine Subgroup.closure_induction (p := fun x _ => x ∈ d8list) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with rfl | rfl | rfl
      · decide +kernel
      · decide +kernel
      · decide +kernel
    · decide +kernel
    · intro y z _ _ hy hz
      exact hcl y hy z hz
    · intro y _ hy
      exact hinv y hy
  · intro hx
    have hsa : sa ∈ d8 := Subgroup.subset_closure (Or.inl rfl)
    have hsb : sb ∈ d8 := Subgroup.subset_closure (Or.inr (Or.inl rfl))
    have hsr : sr ∈ d8 := Subgroup.subset_closure (Or.inr (Or.inr rfl))
    simp only [d8list, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact d8.one_mem
    · exact hsa
    · exact hsb
    · exact d8.mul_mem hsa hsb
    · exact hsr
    · exact d8.mul_mem hsr hsa
    · exact d8.mul_mem hsr hsb
    · exact d8.mul_mem (d8.mul_mem hsr hsa) hsb

theorem isSwap_mem_d8 {x : Perm (Fin 5)} (hx : x ∈ d8) (hs : x.IsSwap) : x = sa ∨ x = sb := by
  have h : ∀ y ∈ d8list, (∃ i j : Fin 5, i ≠ j ∧ y = swap i j) → y = sa ∨ y = sb := by
    decide +kernel
  exact h x (mem_d8_iff.1 hx) hs

theorem card_d8 : Nat.card ↥d8 = 8 := by
  have h1 : (d8 : Set (Perm (Fin 5))) = ↑d8list.toFinset := by
    ext x
    simp only [SetLike.mem_coe, List.mem_toFinset]
    exact mem_d8_iff
  have h2 : Nat.card ↥d8 = (d8 : Set (Perm (Fin 5))).ncard := Nat.card_coe_set_eq _
  rw [h2, h1, Set.ncard_coe_finset]
  decide +kernel

theorem card_e4 : Nat.card ↥e4 = 4 := by
  have h1 : (e4 : Set (Perm (Fin 5))) = ↑e4list.toFinset := by
    ext x
    simp only [SetLike.mem_coe, List.mem_toFinset]
    exact mem_e4_iff
  have h2 : Nat.card ↥e4 = (e4 : Set (Perm (Fin 5))).ncard := Nat.card_coe_set_eq _
  rw [h2, h1, Set.ncard_coe_finset]
  decide +kernel

@[expose] def fixVec (S : Finset (Perm (Fin 5))) : Finset (Fin 5 → ZMod 2) :=
  Finset.univ.filter fun y => (∑ i, y i = 0) ∧ ∀ a ∈ S, ∀ i, y (a⁻¹ i) = y i

theorem fixVec_classify : ∀ S ∈ d8list.toFinset.powerset,
    (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S ∧ a * b = b * a ∧ a * a = 1) → (1 : Perm (Fin 5)) ∈ S →
    S.card * (fixVec S).card ≤ 16 ∧ (S.card * (fixVec S).card = 16 → S ⊆ e4list.toFinset) := by
  decide +kernel

theorem eq_one_of_fixed_all (σ : Perm (Fin 5))
    (h : ∀ y : Fin 5 → ZMod 2, (∑ i, y i = 0) → ∀ i, y (σ⁻¹ i) = y i) : σ = 1 := by
  revert σ
  decide +kernel

theorem fixed_by_all (y : Fin 5 → ZMod 2) (hy : ∑ i, y i = 0)
    (h : ∀ σ : Perm (Fin 5), ∀ i, y (σ⁻¹ i) = y i) : y = 0 := by
  revert y
  decide +kernel

theorem sr_mem_d8 : sr ∈ d8 := Subgroup.subset_closure (Or.inr (Or.inr rfl))

theorem sa_mem_e4 : sa ∈ e4 := Subgroup.subset_closure (Or.inl rfl)

theorem sb_mem_e4 : sb ∈ e4 := Subgroup.subset_closure (Or.inr rfl)

theorem e4_le_d8 : e4 ≤ d8 := by
  refine Subgroup.closure_mono ?_
  intro x hx
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

theorem sa_mem_d8 : sa ∈ d8 := e4_le_d8 sa_mem_e4

theorem sb_mem_d8 : sb ∈ d8 := e4_le_d8 sb_mem_e4

theorem fixed_eps (y : Fin 5 → ZMod 2) (hy : ∑ i, y i = 0)
    (h : ∀ i, y ((sa * sb)⁻¹ i) = y i) :
    (∀ i, y (sa⁻¹ i) = y i) ∧ (∀ i, y (sb⁻¹ i) = y i) := by
  revert y
  decide +kernel

theorem comm_eps (y : Fin 5 → ZMod 2) (hy : ∑ i, y i = 0) :
    (∀ i, (y ((sa * sb)⁻¹ i) - y i) = (y ((sa * sb)⁻¹ (sa⁻¹ i)) - y (sa⁻¹ i))) ∧
    (∀ i, (y ((sa * sb)⁻¹ i) - y i) = (y ((sa * sb)⁻¹ (sb⁻¹ i)) - y (sb⁻¹ i))) := by
  revert y
  decide +kernel

theorem card_fixVec_e4 : (fixVec e4list.toFinset).card = 4 := by decide +kernel

@[expose] def fixΔ (B₀ : Subgroup (Perm (Fin 5))) : Subgroup ↥(coreMod 5) where
  carrier := {y | ∀ σ ∈ B₀, coreAct 5 σ y = y}
  one_mem' := fun σ _ => map_one _
  mul_mem' := by
    intro _ _ ha hb σ hσ
    rw [map_mul, hb σ hσ, ha σ hσ]
  inv_mem' := by
    intro a ha σ hσ
    rw [map_inv, ha σ hσ]

@[expose] def vecOf (y : ↥(coreMod 5)) : Fin 5 → ZMod 2 := Multiplicative.toAdd (y : PermMod 5)

theorem vecOf_injective : Function.Injective vecOf := fun _ _ h =>
  Subtype.ext (Multiplicative.toAdd.injective h)

theorem sum_vecOf (y : ↥(coreMod 5)) : ∑ i, vecOf y i = 0 := mem_coreMod.1 y.2

theorem vecOf_coreAct (σ : Perm (Fin 5)) (y : ↥(coreMod 5)) (i : Fin 5) :
    vecOf (coreAct 5 σ y) i = vecOf y (σ⁻¹ i) := rfl

theorem coreAct_eq_iff {σ : Perm (Fin 5)} {y : ↥(coreMod 5)} :
    coreAct 5 σ y = y ↔ ∀ i, vecOf y (σ⁻¹ i) = vecOf y i := by
  constructor
  · intro h i
    have := congrFun (congrArg vecOf h) i
    rwa [vecOf_coreAct] at this
  · intro h
    apply vecOf_injective
    funext i
    rw [vecOf_coreAct, h i]

@[expose] def ofVec (f : Fin 5 → ZMod 2) (hf : ∑ i, f i = 0) : ↥(coreMod 5) :=
  ⟨Multiplicative.ofAdd f, mem_coreMod.2 hf⟩

theorem card_coreMod : Nat.card ↥(coreMod 5) = 16 := by
  let e : ↥(coreMod 5) ≃ ↥(Finset.univ.filter fun f : Fin 5 → ZMod 2 => ∑ i, f i = 0) :=
    { toFun := fun y => ⟨vecOf y, by simpa using sum_vecOf y⟩
      invFun := fun f => ofVec f.1 (by simpa using (Finset.mem_filter.1 f.2).2)
      left_inv := fun y => vecOf_injective rfl
      right_inv := fun f => Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  decide +kernel

theorem card_fixΔ {B₀ : Subgroup (Perm (Fin 5))} {S : Finset (Perm (Fin 5))}
    (hS : ∀ σ, σ ∈ S ↔ σ ∈ B₀) : Nat.card ↥(fixΔ B₀) = (fixVec S).card := by
  let e : ↥(fixΔ B₀) ≃ ↥(fixVec S) :=
    { toFun := fun y => ⟨vecOf y.1, by
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, sum_vecOf y.1, fun a ha i => ?_⟩
        have := (coreAct_eq_iff).1 (y.2 a ((hS a).1 ha)) i
        exact this⟩
      invFun := fun f => ⟨ofVec f.1 (Finset.mem_filter.1 f.2).2.1, fun σ hσ =>
        (coreAct_eq_iff).2 fun i => (Finset.mem_filter.1 f.2).2.2 σ ((hS σ).2 hσ) i⟩
      left_inv := fun y => Subtype.ext (vecOf_injective rfl)
      right_inv := fun f => Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

end GE23

end CFSG.Quasithin
