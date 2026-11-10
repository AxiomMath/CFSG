module

public import CFSG.Permutation.FiveTransitive.SupportEightInvolutionClosure

public section

namespace CFSG

namespace FiveTransitive.FixedSetConjugateCore

open Equiv MulAction

abbrev Outside {X : Type*} (S : Finset X) := ↥((S : Set X)ᶜ)

private theorem outside_ne {X : Type*} {S : Finset X} {c : X} (hc : c ∈ S)
    (a : Outside S) : a.val ≠ c := by
  intro he
  exact a.property (he ▸ hc)

private theorem support_outside_of_ne
    {X : Type*} [Fintype X] [DecidableEq X]
    (u : Perm X) (S : Finset X) (c : X)
    (hfix : ∀ x ∈ S, x ≠ c → u x = x)
    {a : X} (ha : a ∈ u.support) (hac : a ≠ c) : a ∉ (S : Set X) := by
  intro haS
  exact Perm.mem_support.mp ha (hfix a haS hac)

theorem card_outside {X : Type*} [Fintype X] (S : Finset X) :
    Nat.card (Outside S) = Fintype.card X - S.card := by
  rw [Nat.card_coe_set_eq]
  have h := Set.ncard_add_ncard_compl (S : Set X)
  rw [Set.ncard_coe_finset, Nat.card_eq_fintype_card] at h
  omega

theorem card_moved_outside
    {X : Type*} [Fintype X] [DecidableEq X]
    (u : Perm X) (S : Finset X) (c : X) (hc : c ∈ S)
    (hmove : u c ≠ c) (hfix : ∀ x ∈ S, x ≠ c → u x = x) :
    Nat.card {a : Outside S // u a.val ≠ a.val} = u.support.card - 1 := by
  classical
  let E : {a : Outside S // u a.val ≠ a.val} ≃ ↥(u.support.erase c) :=
    { toFun := fun a => ⟨a.val.val, Finset.mem_erase.mpr
        ⟨outside_ne hc a.val, Perm.mem_support.mpr a.property⟩⟩
      invFun := fun a => ⟨⟨a.val, support_outside_of_ne u S c hfix
        (Finset.mem_erase.mp a.property).2 (Finset.mem_erase.mp a.property).1⟩,
        Perm.mem_support.mp (Finset.mem_erase.mp a.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_erase_of_mem (Perm.mem_support.mpr hmove)]

private theorem card_embedding_both {Y : Type*} [Fintype Y] [DecidableEq Y] (p : Y → Prop) :
    Nat.card {e : Fin 2 ↪ Y // p (e 0) ∧ p (e 1)} =
      (Nat.card {a : Y // p a}).descFactorial 2 := by
  classical
  let B := Finset.univ.filter p
  have hb : Nat.card {a : Y // p a} = B.card := Nat.subtype_card B (by simp [B])
  have he : Nat.card {e : Fin 2 ↪ Y // p (e 0) ∧ p (e 1)} =
      (SupportEightInvolutionClosure.embeddingsInto 2 B).card := by
    apply Nat.subtype_card
    intro e
    simp [SupportEightInvolutionClosure.embeddingsInto, B, Fin.forall_fin_succ]
  rw [he, SupportEightInvolutionClosure.card_embeddingsInto, hb]

theorem card_both_moved_outside
    {X : Type*} [Fintype X] [DecidableEq X]
    (u : Perm X) (S : Finset X) (c : X) (hc : c ∈ S)
    (hmove : u c ≠ c) (hfix : ∀ x ∈ S, x ≠ c → u x = x) :
    Nat.card {e : Fin 2 ↪ Outside S // u (e 0).val ≠ (e 0).val ∧
      u (e 1).val ≠ (e 1).val} = (u.support.card - 1) * (u.support.card - 2) := by
  classical
  let _ := Fintype.ofFinite (Outside S)
  rw [card_embedding_both (fun a : Outside S => u a.val ≠ a.val),
    card_moved_outside u S c hc hmove hfix]
  simp [Nat.descFactorial, Nat.sub_sub, Nat.mul_comm]

private theorem inv_moved {X : Type*} [Fintype X] [DecidableEq X]
    (u : Perm X) {c : X} (hmove : u c ≠ c) :
    u.symm c ∈ u.support ∧ u.symm c ≠ c := by
  have hne : u.symm c ≠ c := by
    intro he
    exact hmove ((congrArg u he).symm.trans (u.apply_symm_apply c))
  refine ⟨?_, hne⟩
  rw [Perm.mem_support]
  intro he
  exact hne (he.symm.trans (u.apply_symm_apply c))

theorem card_to_distinguished
    {X : Type*} [Fintype X] [DecidableEq X]
    (u : Perm X) (S : Finset X) (c : X)
    (hmove : u c ≠ c) (hfix : ∀ x ∈ S, x ≠ c → u x = x) :
    Nat.card {a : Outside S // u a.val = c} = 1 := by
  have hm := inv_moved u hmove
  let a : Outside S := ⟨u.symm c, support_outside_of_ne u S c hfix hm.1 hm.2⟩
  let _ : Unique {b : Outside S // u b.val = c} :=
    { default := ⟨a, u.apply_symm_apply c⟩
      uniq := fun b => Subtype.ext (Subtype.ext
        (u.injective (b.property.trans (u.apply_symm_apply c).symm))) }
  exact Nat.card_unique

theorem card_directed_outside
    {X : Type*} [Fintype X] [DecidableEq X]
    (u : Perm X) (S : Finset X) (c : X) (hc : c ∈ S)
    (hmove : u c ≠ c) (hfix : ∀ x ∈ S, x ≠ c → u x = x) :
    Nat.card {e : Fin 2 ↪ Outside S // u (e 0).val = (e 1).val} =
      u.support.card - 2 := by
  classical
  have hpre := inv_moved u hmove
  let A := (u.support.erase c).erase (u.symm c)
  let f : {e : Fin 2 ↪ Outside S // u (e 0).val = (e 1).val} → A := fun e =>
    ⟨(e.val 0).val, by
      have hne : u (e.val 0).val ≠ (e.val 0).val := by
        intro he
        have he01 : e.val 0 = e.val 1 := Subtype.ext (he.symm.trans e.property)
        exact Fin.zero_ne_one (e.val.injective he01)
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_erase.mpr ⟨outside_ne hc (e.val 0), Perm.mem_support.mpr hne⟩⟩
      intro he
      have hu0 : u (e.val 0).val = c := by rw [he]; exact u.apply_symm_apply c
      exact outside_ne hc (e.val 1) (e.property.symm.trans hu0)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      ext i
      have hzero : (a.val 0).val = (b.val 0).val := congrArg (fun c : A => c.val) hab
      fin_cases i
      · exact hzero
      · exact a.property.symm.trans ((congrArg u hzero).trans b.property)
    · intro a
      have ha := Finset.mem_erase.mp a.property
      have has := Finset.mem_erase.mp ha.2
      have hua : u a.val ≠ c := by
        intro he
        exact ha.1 (u.injective (he.trans (u.apply_symm_apply c).symm))
      let a₀ : Outside S := ⟨a.val, support_outside_of_ne u S c hfix has.2 has.1⟩
      let a₁ : Outside S := ⟨u a.val, support_outside_of_ne u S c hfix
        (Perm.apply_mem_support.mpr has.2) hua⟩
      have hne : a₀ ≠ a₁ := fun he => (Perm.mem_support.mp has.2) (congrArg Subtype.val he).symm
      let e : Fin 2 ↪ Outside S := ⟨![a₀, a₁], by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact (hne hij).elim
        · exact (hne hij.symm).elim
        · rfl⟩
      exact ⟨⟨e, rfl⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe]
  change A.card = _
  dsimp [A]
  rw [Finset.card_erase_of_mem (by simp [hpre.1, hpre.2]),
    Finset.card_erase_of_mem (Perm.mem_support.mpr hmove)]
  omega

theorem card_from_distinguished
    {X : Type*} [Fintype X] [DecidableEq X]
    (u : Perm X) (S : Finset X) (c : X)
    (hmove : u c ≠ c) (hfix : ∀ x ∈ S, x ≠ c → u x = x) :
    Nat.card {a : Outside S // u c = a.val} = 1 := by
  have hm : u c ∈ u.support := Perm.apply_mem_support.mpr (Perm.mem_support.mpr hmove)
  let a : Outside S := ⟨u c, support_outside_of_ne u S c hfix hm hmove⟩
  let _ : Unique {b : Outside S // u c = b.val} :=
    { default := ⟨a, rfl⟩
      uniq := fun b => Subtype.ext (Subtype.ext b.property.symm) }
  exact Nat.card_unique

theorem card_neighbors_distinguished
    {X : Type*} [Fintype X] [DecidableEq X]
    (u : Perm X) (S : Finset X) (c : X)
    (hmove : u c ≠ c) (hfix : ∀ x ∈ S, x ≠ c → u x = x)
    (hnot2 : u (u c) ≠ c) :
    Nat.card {e : Fin 2 ↪ Outside S // u c = (e 0).val ∧ u (e 1).val = c} = 1 := by
  classical
  have hm : u c ∈ u.support := Perm.apply_mem_support.mpr (Perm.mem_support.mpr hmove)
  have hp := inv_moved u hmove
  let a : Outside S := ⟨u c, support_outside_of_ne u S c hfix hm hmove⟩
  let b : Outside S := ⟨u.symm c, support_outside_of_ne u S c hfix hp.1 hp.2⟩
  have hne : a ≠ b := by
    intro he
    exact hnot2 ((congrArg u (congrArg Subtype.val he)).trans (u.apply_symm_apply c))
  let e : Fin 2 ↪ Outside S := ⟨![a,b], by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hne hij).elim
    · exact (hne hij.symm).elim
    · rfl⟩
  let _ : Unique {e : Fin 2 ↪ Outside S // u c = (e 0).val ∧ u (e 1).val = c} :=
    { default := ⟨e, ⟨rfl, u.apply_symm_apply c⟩⟩
      uniq := fun d => by
        apply Subtype.ext
        ext i
        fin_cases i
        · exact d.property.1.symm
        · exact u.injective (d.property.2.trans (u.apply_symm_apply c).symm) }
  exact Nat.card_unique

end FiveTransitive.FixedSetConjugateCore

end CFSG
