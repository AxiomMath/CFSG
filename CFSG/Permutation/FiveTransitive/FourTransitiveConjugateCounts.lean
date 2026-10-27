module

public import CFSG.Permutation.FiveTransitive.ConjugateCounting

public section

namespace CFSG

namespace FiveTransitive.FourTransitiveConjugateCounts

open Equiv MulAction ConjugateCounting

@[expose] abbrev twoPointFixer {X : Type*} (P : Subgroup (Perm X)) (α β : X) :=
  fixingSubgroup P ({α, β} : Set X)

@[expose] def conjugate {X : Type*} {P : Subgroup (Perm X)} {α β : X}
    (u : Perm X) (k : twoPointFixer P α β) : Perm X :=
  (k.val : Perm X) * u * (k.val : Perm X)⁻¹

theorem conjugate_apply_eq_iff {X : Type*} {P : Subgroup (Perm X)} {α β : X}
    (u : Perm X) (k : twoPointFixer P α β) (γ δ : X) :
    conjugate u k γ = δ ↔
      u ((k.val : Perm X).symm γ) = (k.val : Perm X).symm δ := by
  change (k.val : Perm X) (u ((k.val : Perm X).symm γ)) = δ ↔ _
  constructor
  · intro h
    exact (k.val : Perm X).injective (h.trans ((k.val : Perm X).apply_symm_apply δ).symm)
  · intro h
    rw [h]
    exact (k.val : Perm X).apply_symm_apply δ

private theorem fixer_right_inv {X : Type*} {P : Subgroup (Perm X)} {α β : X}
    (k : twoPointFixer P α β) : (k.val : Perm X).symm β = β := by
  have hk : (k.val : Perm X) β = β :=
    (mem_fixingSubgroup_iff P).mp k.property β (by simp)
  apply (k.val : Perm X).injective
  exact ((k.val : Perm X).apply_symm_apply β).trans hk.symm

private theorem remainder_two_transitive {X : Type*} [Fintype X]
    (P : Subgroup (Perm X)) (h4 : MulAction.IsMultiplyPretransitive P X 4)
    {α β : X} (hαβ : α ≠ β) :
    MulAction.IsMultiplyPretransitive (twoPointFixer P α β)
      (SubMulAction.ofFixingSubgroup P ({α, β} : Set X)) 2 := by
  let _ : MulAction.IsMultiplyPretransitive P X 4 := h4
  have hs : ({α, β} : Set X).ncard = 2 := by simp [hαβ]
  exact SubMulAction.ofFixingSubgroup.isMultiplyPretransitive
    (m := 2) (n := 4) P ({α, β} : Set X) (by omega)

theorem card_moved
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h4 : MulAction.IsMultiplyPretransitive P X 4)
    (u : Perm X) {α β γ : X} (hαβ : α ≠ β)
    (huα : u α = α) (huβ : u β ≠ β) (hγα : γ ≠ α) (hγβ : γ ≠ β) :
    Nat.card {k : twoPointFixer P α β // conjugate u k γ ≠ γ} *
      (Fintype.card X - 2) =
      Nat.card (twoPointFixer P α β) * (u.support.card - 1) := by
  classical
  let K := twoPointFixer P α β
  let Y := SubMulAction.ofFixingSubgroup P ({α, β} : Set X)
  let γ₀ : Y := ⟨γ, by change γ ∉ ({α, β} : Set X); simp [hγα, hγβ]⟩
  let _ : MulAction.IsMultiplyPretransitive K Y 2 := remainder_two_transitive P h4 hαβ
  let _ : MulAction.IsPretransitive K Y := MulAction.isPretransitive_of_is_two_pretransitive
  have hc := card_inverse_smul_pred (G := K) γ₀ (fun a : Y => u a.val ≠ a.val)
  have hpred : Nat.card {k : K // u ((k⁻¹ • γ₀ : Y).val) ≠ (k⁻¹ • γ₀ : Y).val} =
      Nat.card {k : twoPointFixer P α β // conjugate u k γ ≠ γ} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl K) (fun k => by
      change (u ((k.val : Perm X).symm γ) ≠ (k.val : Perm X).symm γ) ↔ _
      exact not_congr (conjugate_apply_eq_iff u k γ γ).symm)
  rw [hpred] at hc
  have hY : Nat.card Y = Fintype.card X - 2 := by
    change Nat.card (Remainder α β) = _
    rw [card_remainder hαβ, Nat.card_eq_fintype_card]
  have hb : Nat.card {a : Y // u a.val ≠ a.val} = u.support.card - 1 :=
    card_moved_remainder u huα huβ
  rw [hY, hb] at hc
  exact hc

theorem card_maps_right
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h4 : MulAction.IsMultiplyPretransitive P X 4)
    (u : Perm X) {α β γ : X} (hαβ : α ≠ β)
    (huα : u α = α) (huβ : u β ≠ β) (hγα : γ ≠ α) (hγβ : γ ≠ β) :
    Nat.card {k : twoPointFixer P α β // conjugate u k γ = β} *
      (Fintype.card X - 2) = Nat.card (twoPointFixer P α β) := by
  classical
  let K := twoPointFixer P α β
  let Y := SubMulAction.ofFixingSubgroup P ({α, β} : Set X)
  let γ₀ : Y := ⟨γ, by change γ ∉ ({α, β} : Set X); simp [hγα, hγβ]⟩
  let _ : MulAction.IsMultiplyPretransitive K Y 2 := remainder_two_transitive P h4 hαβ
  let _ : MulAction.IsPretransitive K Y := MulAction.isPretransitive_of_is_two_pretransitive
  have hc := card_inverse_smul_pred (G := K) γ₀ (fun a : Y => u a.val = β)
  have hpred : Nat.card {k : K // u ((k⁻¹ • γ₀ : Y).val) = β} =
      Nat.card {k : twoPointFixer P α β // conjugate u k γ = β} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl K) (fun k => by
      change (u ((k.val : Perm X).symm γ) = β) ↔ _
      rw [conjugate_apply_eq_iff, fixer_right_inv]
      rfl)
  rw [hpred] at hc
  have hY : Nat.card Y = Fintype.card X - 2 := by
    change Nat.card (Remainder α β) = _
    rw [card_remainder hαβ, Nat.card_eq_fintype_card]
  have hb : Nat.card {a : Y // u a.val = β} = 1 :=
    card_to_right_remainder u hαβ huα huβ
  rw [hY, hb, mul_one] at hc
  exact hc

theorem card_maps_other
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h4 : MulAction.IsMultiplyPretransitive P X 4)
    (u : Perm X) {α β γ δ : X} (hαβ : α ≠ β)
    (huα : u α = α) (huβ : u β ≠ β)
    (hγα : γ ≠ α) (hγβ : γ ≠ β) (hδα : δ ≠ α) (hδβ : δ ≠ β) (hγδ : γ ≠ δ) :
    Nat.card {k : twoPointFixer P α β // conjugate u k γ = δ} *
      (Fintype.card X - 2) * (Fintype.card X - 3) =
      Nat.card (twoPointFixer P α β) * (u.support.card - 2) := by
  classical
  let K := twoPointFixer P α β
  let Y := SubMulAction.ofFixingSubgroup P ({α, β} : Set X)
  let γ₀ : Y := ⟨γ, by change γ ∉ ({α, β} : Set X); simp [hγα, hγβ]⟩
  let δ₀ : Y := ⟨δ, by change δ ∉ ({α, β} : Set X); simp [hδα, hδβ]⟩
  have hne : γ₀ ≠ δ₀ := fun he => hγδ (congrArg Subtype.val he)
  let e : Fin 2 ↪ Y := ⟨![γ₀, δ₀], by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hne hij).elim
    · exact (hne hij.symm).elim
    · rfl⟩
  let _ : MulAction.IsMultiplyPretransitive K Y 2 := remainder_two_transitive P h4 hαβ
  have hc := card_inverse_smul_pred (G := K) e
    (fun a : Fin 2 ↪ Y => u (a 0).val = (a 1).val)
  have hpred : Nat.card {k : K // u ((k⁻¹ • e) 0).val = ((k⁻¹ • e) 1).val} =
      Nat.card {k : twoPointFixer P α β // conjugate u k γ = δ} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl K) (fun k => by
      change (u ((k.val : Perm X).symm γ) = (k.val : Perm X).symm δ) ↔ _
      exact (conjugate_apply_eq_iff u k γ δ).symm)
  rw [hpred] at hc
  have hY : Nat.card Y = Fintype.card X - 2 := by
    change Nat.card (Remainder α β) = _
    rw [card_remainder hαβ, Nat.card_eq_fintype_card]
  have hpairs : Nat.card (Fin 2 ↪ Y) = (Fintype.card X - 2) * (Fintype.card X - 3) := by
    let _ := Fintype.ofFinite Y
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
      ← Nat.card_eq_fintype_card, hY]
    simp [Nat.descFactorial, Nat.sub_sub, Nat.mul_comm]
  have hb : Nat.card {a : Fin 2 ↪ Y // u (a 0).val = (a 1).val} = u.support.card - 2 :=
    card_directed_pairs u huα huβ
  rw [hpairs, hb] at hc
  simpa only [mul_assoc] using hc

theorem card_fixed_moved
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h4 : MulAction.IsMultiplyPretransitive P X 4)
    (u : Perm X) {α β γ δ : X} (hαβ : α ≠ β)
    (huα : u α = α) (huβ : u β ≠ β)
    (hγα : γ ≠ α) (hγβ : γ ≠ β) (hδα : δ ≠ α) (hδβ : δ ≠ β) (hγδ : γ ≠ δ) :
    Nat.card {k : twoPointFixer P α β // conjugate u k γ = γ ∧ conjugate u k δ ≠ δ} *
      (Fintype.card X - 2) * (Fintype.card X - 3) =
      Nat.card (twoPointFixer P α β) *
        ((Fintype.card X - u.support.card - 1) * (u.support.card - 1)) := by
  classical
  let K := twoPointFixer P α β
  let Y := SubMulAction.ofFixingSubgroup P ({α, β} : Set X)
  let γ₀ : Y := ⟨γ, by change γ ∉ ({α, β} : Set X); simp [hγα, hγβ]⟩
  let δ₀ : Y := ⟨δ, by change δ ∉ ({α, β} : Set X); simp [hδα, hδβ]⟩
  have hne : γ₀ ≠ δ₀ := fun he => hγδ (congrArg Subtype.val he)
  let e : Fin 2 ↪ Y := ⟨![γ₀, δ₀], by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hne hij).elim
    · exact (hne hij.symm).elim
    · rfl⟩
  let _ : MulAction.IsMultiplyPretransitive K Y 2 := remainder_two_transitive P h4 hαβ
  have hc := card_inverse_smul_pred (G := K) e
    (fun a : Fin 2 ↪ Y => u (a 0).val = (a 0).val ∧ u (a 1).val ≠ (a 1).val)
  have hpred : Nat.card {k : K // u ((k⁻¹ • e) 0).val = ((k⁻¹ • e) 0).val ∧
      u ((k⁻¹ • e) 1).val ≠ ((k⁻¹ • e) 1).val} =
      Nat.card {k : twoPointFixer P α β // conjugate u k γ = γ ∧ conjugate u k δ ≠ δ} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl K) (fun k => by
      change (u ((k.val : Perm X).symm γ) = (k.val : Perm X).symm γ ∧
        u ((k.val : Perm X).symm δ) ≠ (k.val : Perm X).symm δ) ↔ _
      exact and_congr (conjugate_apply_eq_iff u k γ γ).symm
        (not_congr (conjugate_apply_eq_iff u k δ δ).symm))
  rw [hpred] at hc
  have hY : Nat.card Y = Fintype.card X - 2 := by
    change Nat.card (Remainder α β) = _
    rw [card_remainder hαβ, Nat.card_eq_fintype_card]
  have hpairs : Nat.card (Fin 2 ↪ Y) = (Fintype.card X - 2) * (Fintype.card X - 3) := by
    let _ := Fintype.ofFinite Y
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
      ← Nat.card_eq_fintype_card, hY]
    simp [Nat.descFactorial, Nat.sub_sub, Nat.mul_comm]
  have hb : Nat.card {a : Fin 2 ↪ Y // u (a 0).val = (a 0).val ∧ u (a 1).val ≠ (a 1).val} =
      (Fintype.card X - u.support.card - 1) * (u.support.card - 1) :=
    card_fixed_moved_pairs u huα huβ
  rw [hpairs, hb] at hc
  simpa only [mul_assoc] using hc

end FiveTransitive.FourTransitiveConjugateCounts

end CFSG
