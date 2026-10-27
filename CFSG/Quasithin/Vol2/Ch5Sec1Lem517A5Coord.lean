module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13

open Equiv

@[expose] def blk5 (i : Fin 5) : Fin 3 := ⟨i.val / 2, by omega⟩

@[expose] def InD8 (σ : Perm (Fin 5)) : Prop :=
  ∀ i j, blk5 i = blk5 j → blk5 (σ i) = blk5 (σ j)

instance : DecidablePred InD8 := fun σ =>
  inferInstanceAs (Decidable (∀ i j, blk5 i = blk5 j → blk5 (σ i) = blk5 (σ j)))

@[expose] def InE4 (σ : Perm (Fin 5)) : Prop := ∀ i, blk5 (σ i) = blk5 i

instance : DecidablePred InE4 := fun σ => inferInstanceAs (Decidable (∀ i, blk5 (σ i) = blk5 i))

@[expose] def pmv (σ : Perm (Fin 5)) (x : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 := fun i => x (σ⁻¹ i)

theorem pmv_mul (σ τ : Perm (Fin 5)) (x : Fin 5 → ZMod 2) :
    pmv (σ * τ) x = pmv σ (pmv τ x) := by
  funext i
  simp [pmv, mul_inv_rev, Perm.mul_apply]

theorem pmv_one (x : Fin 5 → ZMod 2) : pmv 1 x = x := rfl

@[expose] def FixesD5 (σ : Perm (Fin 5)) : Prop :=
  ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 → pmv σ x = x

instance (σ : Perm (Fin 5)) : Decidable (FixesD5 σ) := by unfold FixesD5; infer_instance

theorem pmv_faithful_aux : ∀ σ : Perm (Fin 5), FixesD5 σ → σ = 1 := by decide +kernel

theorem pmv_faithful (σ : Perm (Fin 5)) (h : ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 → pmv σ x = x) :
    σ = 1 :=
  pmv_faithful_aux σ h

@[expose] def e4Sub : Subgroup (Perm (Fin 5)) where
  carrier := {σ | InE4 σ}
  one_mem' := fun _ => rfl
  mul_mem' := fun {σ τ} hσ hτ i => by
    show blk5 (σ (τ i)) = blk5 i
    rw [hσ (τ i), hτ i]
  inv_mem' := fun {σ} hσ i => by
    show blk5 (σ⁻¹ i) = blk5 i
    have h := hσ (σ⁻¹ i)
    rw [show σ (σ⁻¹ i) = i from σ.apply_symm_apply i] at h
    exact h.symm

theorem mem_e4Sub {σ : Perm (Fin 5)} : σ ∈ e4Sub ↔ InE4 σ := Iff.rfl

theorem inD8_inv : ∀ σ : Perm (Fin 5), InD8 σ → InD8 σ⁻¹ := by decide +kernel

@[expose] def d8Sub : Subgroup (Perm (Fin 5)) where
  carrier := {σ | InD8 σ}
  one_mem' := fun _ _ h => h
  mul_mem' := fun {_ τ} hσ hτ i j hij => hσ (τ i) (τ j) (hτ i j hij)
  inv_mem' := fun {σ} hσ => inD8_inv σ hσ

theorem card_filter_d8 : (Finset.univ.filter InD8).card = 8 := by decide +kernel

theorem card_d8Sub : Nat.card ↥d8Sub = 8 := by
  rw [← card_filter_d8, ← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun σ => by
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩

theorem d8_index : d8Sub.index = 15 := by
  have h1 := d8Sub.index_mul_card
  rw [card_d8Sub, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h1
  have : (5 : ℕ).factorial = 120 := by decide
  omega

theorem exists_conj_d8 (P : Sylow 2 (Perm (Fin 5))) : ∃ h : Perm (Fin 5),
    ∀ σ, σ ∈ (P : Subgroup (Perm (Fin 5))) ↔ h⁻¹ * σ * h ∈ d8Sub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥d8Sub := IsPGroup.of_card (n := 3) (by rw [card_d8Sub]; norm_num)
  have hi : ¬ 2 ∣ d8Sub.index := by rw [d8_index]; decide
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) (hp.toSylow hi) P
  refine ⟨h, fun σ => ?_⟩
  rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.conj_inv_apply]
  rfl

theorem inE4_iff : ∀ σ : Perm (Fin 5), InE4 σ ↔
    (σ = 1 ∨ σ = swap 0 1 ∨ σ = swap 2 3 ∨ σ = swap 0 1 * swap 2 3) := by
  decide +kernel

@[expose] def fixCard1 (σ : Perm (Fin 5)) : ℕ :=
  (Finset.univ.filter fun x : Fin 5 → ZMod 2 => ∑ i, x i = 0 ∧ pmv σ x = x).card

@[expose] def fixCard2 (σ τ : Perm (Fin 5)) : ℕ :=
  (Finset.univ.filter fun x : Fin 5 → ZMod 2 => ∑ i, x i = 0 ∧ pmv σ x = x ∧ pmv τ x = x).card

theorem d5_fix_card_outside : ∀ σ : Perm (Fin 5), InD8 σ → σ * σ = 1 → ¬ InE4 σ →
    fixCard1 σ = 4 := by
  decide +kernel

@[expose] def PairCond (σ τ : Perm (Fin 5)) : Prop :=
  InD8 σ ∧ InD8 τ ∧ σ * σ = 1 ∧ τ * τ = 1 ∧ σ * τ = τ * σ ∧ ¬ InE4 σ ∧ τ ≠ 1 ∧ τ ≠ σ

instance (σ τ : Perm (Fin 5)) : Decidable (PairCond σ τ) := by unfold PairCond; infer_instance

theorem d5_fix_card_pair : ∀ σ τ : Perm (Fin 5), PairCond σ τ → fixCard2 σ τ = 2 := by
  decide +kernel

theorem d5_fix_card_E4 : fixCard2 (swap 0 1) (swap 2 3) = 4 := by decide +kernel

theorem fixCard1_le_eight : ∀ σ : Perm (Fin 5), InE4 σ → σ ≠ 1 → fixCard1 σ ≤ 8 := by
  decide +kernel

theorem d5_transposition_of_fix : ∀ σ : Perm (Fin 5), InE4 σ → σ ≠ 1 → 4 < fixCard1 σ →
    σ = swap 0 1 ∨ σ = swap 2 3 := by
  decide +kernel

@[expose] def FixesCE (σ : Perm (Fin 5)) : Prop :=
  ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 → (∀ ε : Perm (Fin 5), InE4 ε → pmv ε x = x) → pmv σ x = x

instance (σ : Perm (Fin 5)) : Decidable (FixesCE σ) := by unfold FixesCE; infer_instance

theorem d5_centralizer_E4 : ∀ σ : Perm (Fin 5), InD8 σ → FixesCE σ → InE4 σ := by
  decide +kernel

@[expose] def DisjComm (ε₁ ε₂ : Perm (Fin 5)) : Prop :=
  ∀ x y : Fin 5 → ZMod 2, ∑ i, x i = 0 → ∑ i, y i = 0 →
    pmv ε₁ x - x = pmv ε₂ y - y → pmv ε₁ x - x = 0

instance (ε₁ ε₂ : Perm (Fin 5)) : Decidable (DisjComm ε₁ ε₂) := by
  unfold DisjComm; infer_instance

@[expose] def E4Pair (ε₁ ε₂ : Perm (Fin 5)) : Prop :=
  InE4 ε₁ ∧ InE4 ε₂ ∧ ε₁ ≠ 1 ∧ ε₂ ≠ 1 ∧ ε₁ ≠ ε₂

instance (ε₁ ε₂ : Perm (Fin 5)) : Decidable (E4Pair ε₁ ε₂) := by unfold E4Pair; infer_instance

theorem d5_E4_disjoint : ∀ ε₁ ε₂ : Perm (Fin 5), E4Pair ε₁ ε₂ → DisjComm ε₁ ε₂ →
    ε₁ = swap 0 1 ∨ ε₁ = swap 2 3 := by
  decide +kernel

theorem d5_conj_swap : ∀ t : Perm (Fin 5), InD8 t → ¬ InE4 t →
    t * swap 0 1 * t⁻¹ = swap 2 3 ∧ t * swap 2 3 * t⁻¹ = swap 0 1 := by
  decide +kernel

theorem d5_stab_01 : pmv (swap 2 4) ![1, 1, 0, 0, 0] = ![1, 1, 0, 0, 0] ∧
    (swap 2 4 * swap 2 3 * (swap 2 4)⁻¹ : Perm (Fin 5)) ≠ swap 2 3 ∧
    (swap 2 4 * swap 2 3 * (swap 2 4)⁻¹ : Perm (Fin 5)) ≠ 1 := by
  decide +kernel

theorem d5_stab_23 : pmv (swap 0 4) ![0, 0, 1, 1, 0] = ![0, 0, 1, 1, 0] ∧
    (swap 0 4 * swap 0 1 * (swap 0 4)⁻¹ : Perm (Fin 5)) ≠ swap 0 1 ∧
    (swap 0 4 * swap 0 1 * (swap 0 4)⁻¹ : Perm (Fin 5)) ≠ 1 := by
  decide +kernel

end CFSG.Quasithin.H13
