module

public import CFSG.Permutation.FiveTransitive.SupportEightInvolutionClosure

public section

namespace CFSG

namespace FiveTransitive.ConjugateCounting

open Equiv MulAction

theorem card_inverse_smul_pred
    {G Ω : Type*} [Group G] [Finite G] [Finite Ω] [MulAction G Ω]
    [MulAction.IsPretransitive G Ω] (x : Ω) (p : Ω → Prop) :
    Nat.card {g : G // p (g⁻¹ • x)} * Nat.card Ω =
      Nat.card G * Nat.card {y : Ω // p y} := by
  classical
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite Ω
  let B := Finset.univ.filter p
  have hc := SupportEightInvolutionClosure.card_smul_mem_finset (G := G) x B
  have hB : Nat.card {y : Ω // p y} = B.card := Nat.subtype_card B (by simp [B])
  have hC : Nat.card {g : G // p (g • x)} =
      (Finset.univ.filter fun g : G => g • x ∈ B).card :=
    Nat.subtype_card _ (by simp [B])
  have hi : Nat.card {g : G // p (g⁻¹ • x)} = Nat.card {g : G // p (g • x)} :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.inv G) (fun _ => Iff.rfl))
  have horbit : Nat.card Ω * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
    simpa [Nat.card_eq_fintype_card, MulAction.orbit_eq_univ G x] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x
  rw [hi, hC, hc, hB]
  calc
    (B.card * Nat.card (MulAction.stabilizer G x)) * Nat.card Ω =
      (Nat.card Ω * Nat.card (MulAction.stabilizer G x)) * B.card := by ring
    _ = Nat.card G * B.card := by rw [horbit]

private theorem card_embedding_pair_pred
    {Y : Type*} [Finite Y] (p q : Y → Prop)
    (hdis : ∀ a, p a → q a → False) :
    Nat.card {e : Fin 2 ↪ Y // p (e 0) ∧ q (e 1)} =
      Nat.card {a : Y // p a} * Nat.card {b : Y // q b} := by
  classical
  let E : {e : Fin 2 ↪ Y // p (e 0) ∧ q (e 1)} ≃
      ({a : Y // p a} × {b : Y // q b}) :=
    { toFun := fun e => (⟨e.val 0, e.property.1⟩, ⟨e.val 1, e.property.2⟩)
      invFun := fun ab => ⟨⟨![ab.1.val, ab.2.val], by
        have hne : ab.1.val ≠ ab.2.val := fun he => hdis _ (he ▸ ab.1.property) ab.2.property
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact (hne hij).elim
        · exact (hne hij.symm).elim
        · rfl⟩, ⟨ab.1.property, ab.2.property⟩⟩
      left_inv := fun e => by
        apply Subtype.ext
        ext i
        fin_cases i <;> rfl
      right_inv := fun ab => by cases ab; rfl }
  rw [Nat.card_congr E, Nat.card_prod]

abbrev Remainder {X : Type*} (α β : X) := ↥(({α, β} : Set X)ᶜ)

private theorem remainder_ne_left {X : Type*} {α β : X} (a : Remainder α β) : a.val ≠ α := by
  intro h
  exact a.property (by simp [h])

private theorem remainder_ne_right {X : Type*} {α β : X} (a : Remainder α β) : a.val ≠ β := by
  intro h
  exact a.property (by simp [h])

theorem card_remainder {X : Type*} [Finite X] {α β : X} (hαβ : α ≠ β) :
    Nat.card (Remainder α β) = Nat.card X - 2 := by
  rw [Nat.card_coe_set_eq]
  have hs : ({α, β} : Set X).ncard = 2 := by simp [hαβ]
  have h := Set.ncard_add_ncard_compl ({α, β} : Set X)
  omega

theorem card_moved_remainder {X : Type*} [Fintype X] [DecidableEq X]
    (u : Perm X) {α β : X} (huα : u α = α) (huβ : u β ≠ β) :
    Nat.card {a : Remainder α β // u a.val ≠ a.val} = u.support.card - 1 := by
  classical
  have hα : α ∉ u.support := by simpa using huα
  have hβ : β ∈ u.support := Perm.mem_support.mpr huβ
  let E : {a : Remainder α β // u a.val ≠ a.val} ≃ ↥(u.support.erase β) :=
    { toFun := fun a => ⟨a.val.val, Finset.mem_erase.mpr
        ⟨remainder_ne_right a.val, Perm.mem_support.mpr a.property⟩⟩
      invFun := fun a => ⟨⟨a.val, by
        have ha := Finset.mem_erase.mp a.property
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun he => hα (he ▸ ha.2), ha.1⟩⟩,
        Perm.mem_support.mp (Finset.mem_erase.mp a.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_erase_of_mem hβ]

private theorem card_fixed_remainder {X : Type*} [Fintype X] [DecidableEq X]
    (u : Perm X) {α β : X} (huα : u α = α) (huβ : u β ≠ β) :
    Nat.card {a : Remainder α β // u a.val = a.val} =
      Fintype.card X - u.support.card - 1 := by
  classical
  have hα : α ∈ u.supportᶜ := by simpa using huα
  let E : {a : Remainder α β // u a.val = a.val} ≃ ↥(u.supportᶜ.erase α) :=
    { toFun := fun a => ⟨a.val.val, Finset.mem_erase.mpr
        ⟨remainder_ne_left a.val, by simpa using a.property⟩⟩
      invFun := fun a => ⟨⟨a.val, by
        have ha := Finset.mem_erase.mp a.property
        have hafix : u a.val = a.val := by simpa using ha.2
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨ha.1, fun he => huβ (he ▸ hafix)⟩⟩, by
        simpa using (Finset.mem_erase.mp a.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_erase_of_mem hα, Finset.card_compl]

theorem card_to_right_remainder {X : Type*} [Fintype X] [DecidableEq X]
    (u : Perm X) {α β : X} (hαβ : α ≠ β) (huα : u α = α) (huβ : u β ≠ β) :
    Nat.card {a : Remainder α β // u a.val = β} = 1 := by
  have hpa : u.symm β ≠ α := by
    intro he
    have h := u.apply_symm_apply β
    rw [he, huα] at h
    exact hαβ h
  have hpb : u.symm β ≠ β := by
    intro he
    apply huβ
    exact (congrArg u he).symm.trans (u.apply_symm_apply β)
  let a : Remainder α β := ⟨u.symm β, by simp [hpa, hpb]⟩
  have uniq : ∀ b : {b : Remainder α β // u b.val = β}, b = ⟨a, u.apply_symm_apply β⟩ := by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    apply u.injective
    exact b.property.trans (u.apply_symm_apply β).symm
  let _ : Unique {b : Remainder α β // u b.val = β} :=
    { default := ⟨a, u.apply_symm_apply β⟩
      uniq := uniq }
  exact Nat.card_unique

theorem card_fixed_moved_pairs {X : Type*} [Fintype X] [DecidableEq X]
    (u : Perm X) {α β : X} (huα : u α = α) (huβ : u β ≠ β) :
    Nat.card {e : Fin 2 ↪ Remainder α β //
      u (e 0).val = (e 0).val ∧ u (e 1).val ≠ (e 1).val} =
      (Fintype.card X - u.support.card - 1) * (u.support.card - 1) := by
  rw [card_embedding_pair_pred (fun a : Remainder α β => u a.val = a.val)
    (fun a : Remainder α β => u a.val ≠ a.val) (fun a ha hb => hb ha),
    card_fixed_remainder u huα huβ, card_moved_remainder u huα huβ]

theorem card_directed_pairs {X : Type*} [Fintype X] [DecidableEq X]
    (u : Perm X) {α β : X} (huα : u α = α) (huβ : u β ≠ β) :
    Nat.card {e : Fin 2 ↪ Remainder α β // u (e 0).val = (e 1).val} =
      u.support.card - 2 := by
  classical
  have hα : α ∉ u.support := by simpa using huα
  have hβ : β ∈ u.support := Perm.mem_support.mpr huβ
  have hpreβ : u.symm β ∈ u.support := by
    rw [Perm.mem_support]
    intro he
    have he' : β = u.symm β := (u.apply_symm_apply β).symm.trans he
    exact huβ ((congrArg u he').trans (u.apply_symm_apply β))
  have hpre_ne : u.symm β ≠ β := by
    intro he
    exact huβ ((congrArg u he).symm.trans (u.apply_symm_apply β))
  let S := (u.support.erase β).erase (u.symm β)
  let f : {e : Fin 2 ↪ Remainder α β // u (e 0).val = (e 1).val} → S := fun e =>
    ⟨(e.val 0).val, by
      have hne : u (e.val 0).val ≠ (e.val 0).val := by
        intro he
        have he01 : e.val 0 = e.val 1 := Subtype.ext (he.symm.trans e.property)
        have : (0 : Fin 2) = 1 := e.val.injective he01
        exact Fin.zero_ne_one this
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_erase.mpr ⟨remainder_ne_right (e.val 0), Perm.mem_support.mpr hne⟩⟩
      intro he
      have hu0 : u (e.val 0).val = β := by rw [he]; exact u.apply_symm_apply β
      exact remainder_ne_right (e.val 1) (e.property.symm.trans hu0)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      ext i
      have hzero : (a.val 0).val = (b.val 0).val := congrArg (fun c : S => c.val) hab
      fin_cases i
      · exact hzero
      · exact a.property.symm.trans ((congrArg u hzero).trans b.property)
    · intro a
      have ha := Finset.mem_erase.mp a.property
      have has := Finset.mem_erase.mp ha.2
      have haα : a.val ≠ α := fun he => hα (he ▸ has.2)
      have huaα : u a.val ≠ α := by
        intro he
        exact haα (u.injective (he.trans huα.symm))
      have huaβ : u a.val ≠ β := by
        intro he
        exact ha.1 (u.injective (he.trans (u.apply_symm_apply β).symm))
      let a₀ : Remainder α β := ⟨a.val, by simp [haα, has.1]⟩
      let a₁ : Remainder α β := ⟨u a.val, by simp [huaα, huaβ]⟩
      have hne : a₀ ≠ a₁ := by
        intro he
        exact (Perm.mem_support.mp has.2) (congrArg Subtype.val he).symm
      let e : Fin 2 ↪ Remainder α β := ⟨![a₀, a₁], by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact (hne hij).elim
        · exact (hne hij.symm).elim
        · rfl⟩
      exact ⟨⟨e, rfl⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card,
    Fintype.card_coe]
  change S.card = _
  dsimp [S]
  rw [Finset.card_erase_of_mem (by simp [hpre_ne, hpreβ]),
    Finset.card_erase_of_mem hβ]
  omega

end FiveTransitive.ConjugateCounting

end CFSG
