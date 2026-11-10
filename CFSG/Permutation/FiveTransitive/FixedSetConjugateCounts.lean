module

public import CFSG.Permutation.FiveTransitive.ConjugateCounting
public import CFSG.Permutation.FiveTransitive.FixedSetConjugateCore

public section

namespace CFSG

namespace FiveTransitive.FixedSetConjugateCounts

open Equiv MulAction ConjugateCounting FixedSetConjugateCore

abbrev Fixer {X : Type*} (P : Subgroup (Perm X)) (S : Finset X) :=
  fixingSubgroup P (S : Set X)

abbrev Remainder {X : Type*} (P : Subgroup (Perm X)) (S : Finset X) :=
  SubMulAction.ofFixingSubgroup P (S : Set X)

@[expose] def conjugate {X : Type*} {P : Subgroup (Perm X)} {S : Finset X}
    (u : Perm X) (k : Fixer P S) : Perm X :=
  (k.val : Perm X) * u * (k.val : Perm X)⁻¹

theorem conjugate_apply_eq_iff {X : Type*} {P : Subgroup (Perm X)} {S : Finset X}
    (u : Perm X) (k : Fixer P S) (γ δ : X) :
    conjugate u k γ = δ ↔
      u ((k.val : Perm X).symm γ) = (k.val : Perm X).symm δ := by
  change (k.val : Perm X) (u ((k.val : Perm X).symm γ)) = δ ↔ _
  constructor
  · intro h
    exact (k.val : Perm X).injective (h.trans ((k.val : Perm X).apply_symm_apply δ).symm)
  · intro h
    rw [h]
    exact (k.val : Perm X).apply_symm_apply δ

theorem fixer_inv {X : Type*} {P : Subgroup (Perm X)} {S : Finset X}
    (k : Fixer P S) {c : X} (hc : c ∈ S) : (k.val : Perm X).symm c = c := by
  have hk : (k.val : Perm X) c = c := (mem_fixingSubgroup_iff P).mp k.property c hc
  apply (k.val : Perm X).injective
  exact ((k.val : Perm X).apply_symm_apply c).trans hk.symm

theorem remainder_two_transitive {X : Type*} [Fintype X]
    (P : Subgroup (Perm X)) (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (S : Finset X) (hS : S.card = 3) :
    MulAction.IsMultiplyPretransitive (Fixer P S) (Remainder P S) 2 := by
  let _ : MulAction.IsMultiplyPretransitive P X 5 := h5
  have hs : (S : Set X).ncard = 3 := by simpa using hS
  exact SubMulAction.ofFixingSubgroup.isMultiplyPretransitive
    (m := 2) (n := 5) P (S : Set X) (by omega)

private theorem card_pairs {X : Type*} [Fintype X] (P : Subgroup (Perm X)) (S : Finset X) :
    Nat.card (Fin 2 ↪ Remainder P S) =
      (Fintype.card X - S.card) * (Fintype.card X - S.card - 1) := by
  classical
  let _ := Fintype.ofFinite (Remainder P S)
  rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
    ← Nat.card_eq_fintype_card]
  change (Nat.card (Outside S)).descFactorial 2 = _
  rw [card_outside]
  simp [Nat.descFactorial, Nat.mul_comm]

theorem card_moved
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (S : Finset X)
    (h2 : MulAction.IsMultiplyPretransitive (Fixer P S) (Remainder P S) 2)
    (u : Perm X) {c γ : X} (hc : c ∈ S)
    (hmove : u c ≠ c) (hfix : ∀ x ∈ S, x ≠ c → u x = x) (hγ : γ ∉ S) :
    Nat.card {k : Fixer P S // conjugate u k γ ≠ γ} *
      (Fintype.card X - S.card) = Nat.card (Fixer P S) * (u.support.card - 1) := by
  classical
  let K := Fixer P S
  let Y := Remainder P S
  let γ₀ : Y := ⟨γ, hγ⟩
  let _ : MulAction.IsMultiplyPretransitive K Y 2 := h2
  let _ : MulAction.IsPretransitive K Y := MulAction.isPretransitive_of_is_two_pretransitive
  have hn := card_inverse_smul_pred (G := K) γ₀ (fun a : Y => u a.val ≠ a.val)
  have hp : Nat.card {k : K // u ((k⁻¹ • γ₀ : Y).val) ≠ (k⁻¹ • γ₀ : Y).val} =
      Nat.card {k : Fixer P S // conjugate u k γ ≠ γ} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl K) (fun k => by
      change (u ((k.val : Perm X).symm γ) ≠ (k.val : Perm X).symm γ) ↔ _
      exact not_congr (conjugate_apply_eq_iff u k γ γ).symm)
  have hY : Nat.card Y = Fintype.card X - S.card := card_outside S
  have hb : Nat.card {a : Y // u a.val ≠ a.val} = u.support.card - 1 :=
    card_moved_outside u S c hc hmove hfix
  rwa [hp, hY, hb] at hn

theorem card_maps_distinguished
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (S : Finset X)
    (h2 : MulAction.IsMultiplyPretransitive (Fixer P S) (Remainder P S) 2)
    (u : Perm X) {c γ : X} (hc : c ∈ S)
    (hmove : u c ≠ c) (hfix : ∀ x ∈ S, x ≠ c → u x = x) (hγ : γ ∉ S) :
    Nat.card {k : Fixer P S // conjugate u k γ = c} *
      (Fintype.card X - S.card) = Nat.card (Fixer P S) := by
  classical
  let K := Fixer P S
  let Y := Remainder P S
  let γ₀ : Y := ⟨γ, hγ⟩
  let _ : MulAction.IsMultiplyPretransitive K Y 2 := h2
  let _ : MulAction.IsPretransitive K Y := MulAction.isPretransitive_of_is_two_pretransitive
  have hn := card_inverse_smul_pred (G := K) γ₀ (fun a : Y => u a.val = c)
  have hp : Nat.card {k : K // u ((k⁻¹ • γ₀ : Y).val) = c} =
      Nat.card {k : Fixer P S // conjugate u k γ = c} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl K) (fun k => by
      change (u ((k.val : Perm X).symm γ) = c) ↔ _
      simpa only [Equiv.refl_apply, fixer_inv k hc] using
        (conjugate_apply_eq_iff u k γ c).symm)
  have hY : Nat.card Y = Fintype.card X - S.card := card_outside S
  have hb : Nat.card {a : Y // u a.val = c} = 1 :=
    card_to_distinguished u S c hmove hfix
  simpa only [hp, hY, hb, mul_one] using hn

theorem card_maps_other
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (S : Finset X)
    (h2 : MulAction.IsMultiplyPretransitive (Fixer P S) (Remainder P S) 2)
    (u : Perm X) {c γ δ : X} (hc : c ∈ S)
    (hmove : u c ≠ c) (hfix : ∀ x ∈ S, x ≠ c → u x = x)
    (hγ : γ ∉ S) (hδ : δ ∉ S) (hγδ : γ ≠ δ) :
    Nat.card {k : Fixer P S // conjugate u k γ = δ} *
      (Fintype.card X - S.card) * (Fintype.card X - S.card - 1) =
      Nat.card (Fixer P S) * (u.support.card - 2) := by

  classical
  let K := Fixer P S
  let Y := Remainder P S
  let γ₀ : Y := ⟨γ, hγ⟩
  let δ₀ : Y := ⟨δ, hδ⟩
  have hne : γ₀ ≠ δ₀ := fun he => hγδ (congrArg Subtype.val he)
  let e : Fin 2 ↪ Y := ⟨![γ₀, δ₀], by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hne hij).elim
    · exact (hne hij.symm).elim
    · rfl⟩
  let _ : MulAction.IsMultiplyPretransitive K Y 2 := h2

  have hn := card_inverse_smul_pred (G := K) e
    (fun a : Fin 2 ↪ Y => u (a 0).val = (a 1).val)
  have hp : Nat.card {k : K // u ((k⁻¹ • e) 0).val = ((k⁻¹ • e) 1).val} =
      Nat.card {k : Fixer P S // conjugate u k γ = δ} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl K) (fun k => by
      change (u ((k.val : Perm X).symm γ) = ((k.val : Perm X).symm δ)) ↔ _
      exact (conjugate_apply_eq_iff u k γ δ).symm)
  have hb : Nat.card {a : Fin 2 ↪ Y // u (a 0).val = (a 1).val} = u.support.card - 2 :=
    card_directed_outside u S c hc hmove hfix
  rw [hp, card_pairs P S, hb] at hn
  simpa only [mul_assoc] using hn

theorem card_both_moved
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (S : Finset X)
    (h2 : MulAction.IsMultiplyPretransitive (Fixer P S) (Remainder P S) 2)
    (u : Perm X) {c γ δ : X} (hc : c ∈ S)
    (hmove : u c ≠ c) (hfix : ∀ x ∈ S, x ≠ c → u x = x)
    (hγ : γ ∉ S) (hδ : δ ∉ S) (hγδ : γ ≠ δ) :
    Nat.card {k : Fixer P S // conjugate u k γ ≠ γ ∧ conjugate u k δ ≠ δ} *
      (Fintype.card X - S.card) * (Fintype.card X - S.card - 1) =
      Nat.card (Fixer P S) * ((u.support.card - 1) * (u.support.card - 2)) := by

  classical
  let K := Fixer P S
  let Y := Remainder P S
  let γ₀ : Y := ⟨γ, hγ⟩
  let δ₀ : Y := ⟨δ, hδ⟩
  have hne : γ₀ ≠ δ₀ := fun he => hγδ (congrArg Subtype.val he)
  let e : Fin 2 ↪ Y := ⟨![γ₀, δ₀], by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hne hij).elim
    · exact (hne hij.symm).elim
    · rfl⟩
  let _ : MulAction.IsMultiplyPretransitive K Y 2 := h2

  have hn := card_inverse_smul_pred (G := K) e
    (fun a : Fin 2 ↪ Y => u (a 0).val ≠ (a 0).val ∧ u (a 1).val ≠ (a 1).val)
  have hp : Nat.card {k : K // u ((k⁻¹ • e) 0).val ≠ ((k⁻¹ • e) 0).val ∧ u ((k⁻¹ • e) 1).val ≠ ((k⁻¹ • e) 1).val} =
      Nat.card {k : Fixer P S // conjugate u k γ ≠ γ ∧ conjugate u k δ ≠ δ} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl K) (fun k => by
      change (u ((k.val : Perm X).symm γ) ≠ ((k.val : Perm X).symm γ) ∧ u ((k.val : Perm X).symm δ) ≠ ((k.val : Perm X).symm δ)) ↔ _
      exact and_congr (not_congr (conjugate_apply_eq_iff u k γ γ).symm)
        (not_congr (conjugate_apply_eq_iff u k δ δ).symm))
  have hb : Nat.card {a : Fin 2 ↪ Y // u (a 0).val ≠ (a 0).val ∧ u (a 1).val ≠ (a 1).val} = (u.support.card - 1) * (u.support.card - 2) :=
    card_both_moved_outside u S c hc hmove hfix
  rw [hp, card_pairs P S, hb] at hn
  simpa only [mul_assoc] using hn

theorem card_maps_from_distinguished
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (S : Finset X)
    (h2 : MulAction.IsMultiplyPretransitive (Fixer P S) (Remainder P S) 2)
    (u : Perm X) {c γ : X} (hc : c ∈ S)
    (hmove : u c ≠ c) (hfix : ∀ x ∈ S, x ≠ c → u x = x) (hγ : γ ∉ S) :
    Nat.card {k : Fixer P S // conjugate u k c = γ} *
      (Fintype.card X - S.card) = Nat.card (Fixer P S) := by
  classical
  let K := Fixer P S
  let Y := Remainder P S
  let γ₀ : Y := ⟨γ, hγ⟩
  let _ : MulAction.IsMultiplyPretransitive K Y 2 := h2
  let _ : MulAction.IsPretransitive K Y := MulAction.isPretransitive_of_is_two_pretransitive
  have hn := card_inverse_smul_pred (G := K) γ₀ (fun a : Y => u c = a.val)
  have hp : Nat.card {k : K // u c = ((k⁻¹ • γ₀ : Y).val)} =
      Nat.card {k : Fixer P S // conjugate u k c = γ} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl K) (fun k => by
      change (u c = ((k.val : Perm X).symm γ)) ↔ _
      simpa only [Equiv.refl_apply, fixer_inv k hc] using
        (conjugate_apply_eq_iff u k c γ).symm)
  have hY : Nat.card Y = Fintype.card X - S.card := card_outside S
  have hb : Nat.card {a : Y // u c = a.val} = 1 :=
    card_from_distinguished u S c hmove hfix
  simpa only [hp, hY, hb, mul_one] using hn

theorem card_neighbors_distinguished
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (S : Finset X)
    (h2 : MulAction.IsMultiplyPretransitive (Fixer P S) (Remainder P S) 2)
    (u : Perm X) {c γ δ : X} (hc : c ∈ S)
    (hmove : u c ≠ c) (hfix : ∀ x ∈ S, x ≠ c → u x = x)
    (hnot2 : u (u c) ≠ c)
    (hγ : γ ∉ S) (hδ : δ ∉ S) (hγδ : γ ≠ δ) :
    Nat.card {k : Fixer P S // conjugate u k c = γ ∧ conjugate u k δ = c} *
      (Fintype.card X - S.card) * (Fintype.card X - S.card - 1) =
      Nat.card (Fixer P S) := by

  classical
  let K := Fixer P S
  let Y := Remainder P S
  let γ₀ : Y := ⟨γ, hγ⟩
  let δ₀ : Y := ⟨δ, hδ⟩
  have hne : γ₀ ≠ δ₀ := fun he => hγδ (congrArg Subtype.val he)
  let e : Fin 2 ↪ Y := ⟨![γ₀, δ₀], by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hne hij).elim
    · exact (hne hij.symm).elim
    · rfl⟩
  let _ : MulAction.IsMultiplyPretransitive K Y 2 := h2

  have hn := card_inverse_smul_pred (G := K) e
    (fun a : Fin 2 ↪ Y => u c = (a 0).val ∧ u (a 1).val = c)
  have hp : Nat.card {k : K // u c = ((k⁻¹ • e) 0).val ∧ u ((k⁻¹ • e) 1).val = c} =
      Nat.card {k : Fixer P S // conjugate u k c = γ ∧ conjugate u k δ = c} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl K) (fun k => by
      change (u c = ((k.val : Perm X).symm γ) ∧ u ((k.val : Perm X).symm δ) = c) ↔ _
      simpa only [Equiv.refl_apply, fixer_inv k hc] using
        and_congr (conjugate_apply_eq_iff u k c γ).symm
          (conjugate_apply_eq_iff u k δ c).symm)
  have hb : Nat.card {a : Fin 2 ↪ Y // u c = (a 0).val ∧ u (a 1).val = c} = 1 :=
    FixedSetConjugateCore.card_neighbors_distinguished u S c hmove hfix hnot2
  rw [hp, card_pairs P S, hb] at hn
  simpa only [mul_assoc, mul_one] using hn

theorem conjugate_mem {X : Type*} {P : Subgroup (Perm X)} {S : Finset X}
    (u : Perm X) (hu : u ∈ P) (k : Fixer P S) : conjugate u k ∈ P :=
  P.mul_mem (P.mul_mem k.val.property hu) (P.inv_mem k.val.property)

theorem conjugate_fixed {X : Type*} {P : Subgroup (Perm X)} {S : Finset X}
    (u : Perm X) (k : Fixer P S) {x : X} (hx : x ∈ S) (hu : u x=x) :
    conjugate u k x=x := by
  rw [conjugate_apply_eq_iff,fixer_inv k hx]
  exact hu

theorem conjugate_moved {X : Type*} {P : Subgroup (Perm X)} {S : Finset X}
    (u : Perm X) (k : Fixer P S) {x : X} (hx : x ∈ S) (hu : u x≠x) :
    conjugate u k x≠x := by
  rw [ne_eq,conjugate_apply_eq_iff,fixer_inv k hx]
  exact hu

theorem conjugate_order {X : Type*} {P : Subgroup (Perm X)} {S : Finset X}
    (u : Perm X) (k : Fixer P S) : orderOf (conjugate u k)=orderOf u := by
  exact (SemiconjBy.orderOf_eq (k.val : Perm X) (x := u) (y := conjugate u k) (by
    change (k.val : Perm X) * u = ((k.val : Perm X) * u * (k.val : Perm X)⁻¹) * (k.val : Perm X)
    group)).symm

end FiveTransitive.FixedSetConjugateCounts

end CFSG
