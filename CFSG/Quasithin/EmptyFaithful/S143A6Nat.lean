module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.S143

@[expose] def n6Sub : Subgroup (Multiplicative (Fin 6 → ZMod 2)) where
  carrier := {w | (∑ i, Multiplicative.toAdd w i = 0) ∧ Multiplicative.toAdd w 5 = 0}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · simp only [toAdd_mul, Pi.add_apply, Finset.sum_add_distrib, ha1, hb1, add_zero]
    · simp [ha2, hb2]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩ <;> simp [ha1, ha2]

abbrev N6 : Type := ↥n6Sub

instance instDecidableMemN6Sub : DecidablePred (· ∈ n6Sub) := fun w =>
  inferInstanceAs
    (Decidable ((∑ i, Multiplicative.toAdd w i = 0) ∧ Multiplicative.toAdd w 5 = 0))

theorem mem_n6Sub_iff {w : Multiplicative (Fin 6 → ZMod 2)} :
    w ∈ n6Sub ↔ (∑ i, Multiplicative.toAdd w i = 0) ∧ Multiplicative.toAdd w 5 = 0 := Iff.rfl

private theorem zmod_two_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

@[expose] def n6Norm (σ : Equiv.Perm (Fin 6)) (u : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  fun i => u (σ⁻¹ i) + u (σ⁻¹ 5)

theorem n6Norm_add (σ : Equiv.Perm (Fin 6)) (u u' : Fin 6 → ZMod 2) :
    n6Norm σ (u + u') = n6Norm σ u + n6Norm σ u' := by
  funext i
  simp only [n6Norm, Pi.add_apply]
  ring

theorem n6Norm_mul (σ τ : Equiv.Perm (Fin 6)) (u : Fin 6 → ZMod 2) :
    n6Norm σ (n6Norm τ u) = n6Norm (σ * τ) u := by
  funext i
  simp only [n6Norm, mul_inv_rev, Equiv.Perm.coe_mul, Function.comp_apply]
  rw [add_add_add_comm, zmod_two_add_self, add_zero]

theorem n6Norm_one (u : Fin 6 → ZMod 2) (hu : u 5 = 0) : n6Norm 1 u = u := by
  funext i
  simp [n6Norm, hu]

theorem n6Norm_last (σ : Equiv.Perm (Fin 6)) (u : Fin 6 → ZMod 2) : n6Norm σ u 5 = 0 :=
  zmod_two_add_self _

theorem n6Norm_sum (σ : Equiv.Perm (Fin 6)) (u : Fin 6 → ZMod 2) :
    ∑ i, n6Norm σ u i = ∑ i, u i := by
  simp only [n6Norm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Equiv.sum_comp σ⁻¹ u]
  have : (6 : ℕ) • u (σ⁻¹ 5) = 0 := by
    generalize u (σ⁻¹ 5) = x
    revert x
    decide
  rw [this, add_zero]

@[expose] def n6Fun (σ : Equiv.Perm (Fin 6)) (a : N6) : N6 :=
  ⟨Multiplicative.ofAdd (n6Norm σ (Multiplicative.toAdd a.1)),
    mem_n6Sub_iff.2 ⟨by
      rw [toAdd_ofAdd, n6Norm_sum]
      exact (mem_n6Sub_iff.1 a.2).1, n6Norm_last σ _⟩⟩

theorem n6Fun_mul (σ : Equiv.Perm (Fin 6)) (a b : N6) :
    n6Fun σ (a * b) = n6Fun σ a * n6Fun σ b := by
  apply Subtype.ext
  show Multiplicative.ofAdd (n6Norm σ (Multiplicative.toAdd (a.1 * b.1))) =
    Multiplicative.ofAdd (n6Norm σ (Multiplicative.toAdd a.1)) *
      Multiplicative.ofAdd (n6Norm σ (Multiplicative.toAdd b.1))
  rw [toAdd_mul, n6Norm_add, ofAdd_add]

theorem n6Fun_n6Fun (σ τ : Equiv.Perm (Fin 6)) (a : N6) :
    n6Fun σ (n6Fun τ a) = n6Fun (σ * τ) a := by
  apply Subtype.ext
  show Multiplicative.ofAdd (n6Norm σ (n6Norm τ (Multiplicative.toAdd a.1))) =
    Multiplicative.ofAdd (n6Norm (σ * τ) (Multiplicative.toAdd a.1))
  rw [n6Norm_mul]

theorem n6Fun_one (a : N6) : n6Fun 1 a = a := by
  apply Subtype.ext
  show Multiplicative.ofAdd (n6Norm 1 (Multiplicative.toAdd a.1)) = a.1
  rw [n6Norm_one _ (mem_n6Sub_iff.1 a.2).2]
  rfl

@[expose] def n6Equiv (σ : Equiv.Perm (Fin 6)) : N6 ≃* N6 where
  toFun := n6Fun σ
  invFun := n6Fun σ⁻¹
  left_inv a := by rw [n6Fun_n6Fun, inv_mul_cancel, n6Fun_one]
  right_inv a := by rw [n6Fun_n6Fun, mul_inv_cancel, n6Fun_one]
  map_mul' := n6Fun_mul σ

@[expose] def n6Act : Equiv.Perm (Fin 6) →* MulAut N6 where
  toFun := n6Equiv
  map_one' := MulEquiv.ext n6Fun_one
  map_mul' σ τ := MulEquiv.ext fun a => (n6Fun_n6Fun σ τ a).symm

theorem n6Act_val (σ : Equiv.Perm (Fin 6)) (a : N6) (i : Fin 6) :
    Multiplicative.toAdd (n6Act σ a).1 i =
      Multiplicative.toAdd a.1 (σ⁻¹ i) + Multiplicative.toAdd a.1 (σ⁻¹ 5) := rfl

theorem n6Act_eq_iff (σ : Equiv.Perm (Fin 6)) (a b : N6) :
    n6Act σ a = b ↔ ∃ c : ZMod 2, ∀ i : Fin 6,
      Multiplicative.toAdd b.1 i = Multiplicative.toAdd a.1 (σ⁻¹ i) + c := by
  constructor
  · rintro rfl
    exact ⟨_, n6Act_val σ a⟩
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    have h5 : Multiplicative.toAdd a.1 (σ⁻¹ 5) = c := by
      have h := hc 5
      rw [(mem_n6Sub_iff.1 b.2).2] at h
      calc Multiplicative.toAdd a.1 (σ⁻¹ 5)
          = Multiplicative.toAdd a.1 (σ⁻¹ 5) + (Multiplicative.toAdd a.1 (σ⁻¹ 5) + c) := by
            rw [← h, add_zero]
        _ = c := by
            rw [← add_assoc, zmod_two_add_self, zero_add]
    rw [hc i, n6Act_val, h5]

theorem n6_card : Nat.card N6 = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem n6_mul_self (a : N6) : a * a = 1 := by
  apply Subtype.ext
  show Multiplicative.ofAdd (Multiplicative.toAdd a.1 + Multiplicative.toAdd a.1) = 1
  rw [show Multiplicative.toAdd a.1 + Multiplicative.toAdd a.1 = 0 from by
    funext i
    exact zmod_two_add_self _]
  rfl

theorem n6_faithful_perm :
    ∀ σ : Equiv.Perm (Fin 6), (∀ a : N6, n6Act σ a = a) → σ = 1 := by
  decide +kernel

theorem n6_faithful : ∀ σ ∈ alternatingGroup (Fin 6), n6Act σ = 1 → σ = 1 := by
  intro σ _ h
  refine n6_faithful_perm σ fun a => ?_
  rw [h]
  rfl

private def n6Base : N6 := ⟨Multiplicative.ofAdd ![1, 1, 0, 0, 0, 0], by decide⟩

private theorem n6_exists_perm :
    ∀ a : N6, a ≠ 1 → ∃ σ : Equiv.Perm (Fin 6), n6Act σ n6Base = a ∧ Equiv.Perm.sign σ = 1 := by
  decide +kernel

theorem n6_transitive :
    ∀ a b : N6, a ≠ 1 → b ≠ 1 → ∃ σ ∈ alternatingGroup (Fin 6), n6Act σ a = b := by
  intro a b ha hb
  obtain ⟨σ, hσa, hσs⟩ := n6_exists_perm a ha
  obtain ⟨τ, hτb, hτs⟩ := n6_exists_perm b hb
  refine ⟨τ * σ⁻¹, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hσs, hτs]
    rfl
  · rw [map_mul, map_inv, MulAut.mul_apply, ← hσa]
    simp [← hτb]

private theorem n6_invol_perm :
    ∀ σ : Equiv.Perm (Fin 6), σ * σ = 1 → σ ≠ 1 → Equiv.Perm.sign σ = 1 →
      (Finset.univ.filter (fun a : N6 => n6Act σ a = a)).card = 4 ∧
        ∀ a : N6, n6Act σ a = a → ∃ b : N6, a = n6Act σ b * b⁻¹ := by
  decide +kernel

theorem n6_invol :
    ∀ σ ∈ alternatingGroup (Fin 6), σ ≠ 1 → σ * σ = 1 →
      Nat.card {a : N6 // n6Act σ a = a} = 4 ∧
        ∀ a : N6, n6Act σ a = a → ∃ b : N6, a = n6Act σ b * b⁻¹ := by
  intro σ hσ h1 h2
  obtain ⟨hcard, hmem⟩ := n6_invol_perm σ h2 h1 (Equiv.Perm.mem_alternatingGroup.1 hσ)
  refine ⟨?_, hmem⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hcard

private theorem alt6_invol_conj_base :
    ∀ σ : Equiv.Perm (Fin 6), σ * σ = 1 → σ ≠ 1 → Equiv.Perm.sign σ = 1 →
      ∃ ρ : Equiv.Perm (Fin 6),
        ρ * (Equiv.swap 0 1 * Equiv.swap 2 3) * ρ⁻¹ = σ ∧ Equiv.Perm.sign ρ = 1 := by
  decide +kernel

theorem alt6_invol_conj :
    ∀ σ τ : Equiv.Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) → τ ∈ alternatingGroup (Fin 6) →
      σ ≠ 1 → τ ≠ 1 → σ * σ = 1 → τ * τ = 1 →
        ∃ ρ ∈ alternatingGroup (Fin 6), ρ * σ * ρ⁻¹ = τ := by
  intro σ τ hσ hτ hσ1 hτ1 hσ2 hτ2
  obtain ⟨ρ, hρσ, hρs⟩ :=
    alt6_invol_conj_base σ hσ2 hσ1 (Equiv.Perm.mem_alternatingGroup.1 hσ)
  obtain ⟨π, hπτ, hπs⟩ :=
    alt6_invol_conj_base τ hτ2 hτ1 (Equiv.Perm.mem_alternatingGroup.1 hτ)
  refine ⟨π * ρ⁻¹, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hρs, hπs]
    rfl
  · rw [← hρσ, ← hπτ]
    group

end CFSG.Quasithin.S143
