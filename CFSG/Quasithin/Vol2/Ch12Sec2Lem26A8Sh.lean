module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG.Quasithin.H13.Lem26A8

section Shapiro

variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

theorem exists_coboundary_of_pretransitive [MulAction.IsPretransitive Γ X] (x₀ : X)
    (hhom : ∀ φ : MulAction.stabilizer Γ x₀ →* Multiplicative (ZMod 2), φ = 1)
    (c : Γ → X → ZMod 2) (hc : ∀ g h y, c (g * h) y = c g y + c h (g⁻¹ • y)) :
    ∃ e : X → ZMod 2, ∀ g y, c g y = e (g⁻¹ • y) + e y := by
  classical
  have c1 : ∀ y, c 1 y = 0 := by
    intro y
    have h := hc 1 1 y
    rw [one_mul, inv_one, one_smul] at h
    revert h
    generalize c 1 y = a
    revert a
    decide
  let φ : MulAction.stabilizer Γ x₀ →* Multiplicative (ZMod 2) :=
    { toFun := fun h => Multiplicative.ofAdd (c h x₀)
      map_one' := by
        show Multiplicative.ofAdd (c 1 x₀) = 1
        rw [c1, ofAdd_zero]
      map_mul' := fun a b => by
        have ha : (a : Γ)⁻¹ • x₀ = x₀ := by
          rw [inv_smul_eq_iff, MulAction.mem_stabilizer_iff.mp a.2]
        show Multiplicative.ofAdd (c ((a : Γ) * b) x₀) =
          Multiplicative.ofAdd (c a x₀) * Multiplicative.ofAdd (c b x₀)
        rw [hc, ha, ← ofAdd_add] }
  have hφ : ∀ h : Γ, h • x₀ = x₀ → c h x₀ = 0 := by
    intro h hh
    have := congrArg (fun ψ : MulAction.stabilizer Γ x₀ →* Multiplicative (ZMod 2) =>
      Multiplicative.toAdd (ψ ⟨h, MulAction.mem_stabilizer_iff.mpr hh⟩)) (hhom φ)
    simpa [φ] using this
  choose k hk using fun y => MulAction.exists_smul_eq Γ x₀ y
  refine ⟨fun y => c (k y) y, fun g y => ?_⟩
  set y' := g⁻¹ • y with hy'
  have e1 := hc g⁻¹ (k y) y'
  rw [inv_inv, hy', smul_inv_smul] at e1
  have hh : ((k y')⁻¹ * (g⁻¹ * k y)) • x₀ = x₀ := by
    rw [mul_smul, mul_smul, hk y, inv_smul_eq_iff, hk y']
  have e2 := hc (k y') ((k y')⁻¹ * (g⁻¹ * k y)) y'
  have e3 : (k y')⁻¹ • y' = x₀ := by rw [inv_smul_eq_iff, hk y']
  rw [mul_inv_cancel_left, e3, hφ _ hh, add_zero] at e2
  have e4 := hc g g⁻¹ y
  rw [mul_inv_cancel, c1] at e4
  show c g y = c (k y') y' + c (k y) y
  rw [← e2, e1]
  revert e4
  generalize c g y = A
  generalize c g⁻¹ y' = B
  generalize c (k y) y = C
  revert A B C
  decide

end Shapiro

section Alternating

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem alternatingGroup_stabilizer_hom_eq_one (p : α)
    (φ : MulAction.stabilizer (alternatingGroup α) p →* Multiplicative (ZMod 2)) : φ = 1 := by
  have hι : ∀ τ : Equiv.Perm {x // x ≠ p}, τ ∈ alternatingGroup {x // x ≠ p} →
      Equiv.Perm.ofSubtype τ ∈ alternatingGroup α := fun τ hτ => by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
    exact hτ
  have hιp : ∀ τ : Equiv.Perm {x // x ≠ p}, Equiv.Perm.ofSubtype τ p = p := fun τ =>
    Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simp)
  have hst : ∀ (τ : Equiv.Perm {x // x ≠ p}) (hτ : Equiv.Perm.ofSubtype τ ∈ alternatingGroup α),
      (⟨Equiv.Perm.ofSubtype τ, hτ⟩ : alternatingGroup α) ∈ MulAction.stabilizer _ p := by
    intro τ hτ
    rw [MulAction.mem_stabilizer_iff]
    exact hιp τ
  have hx3 : ∀ x : Multiplicative (ZMod 2), x ^ 3 = 1 → x = 1 := by decide
  have key : ∀ τ : Equiv.Perm {x // x ≠ p},
      τ ∈ Subgroup.closure {σ : Equiv.Perm {x // x ≠ p} | σ.IsThreeCycle} →
      ∀ hτ : Equiv.Perm.ofSubtype τ ∈ alternatingGroup α, φ ⟨_, hst τ hτ⟩ = 1 := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem σ hσ =>
      intro h
      apply hx3
      rw [← map_pow]
      have h3 : σ ^ 3 = 1 := by
        rw [← (show σ.IsThreeCycle from hσ).orderOf]
        exact pow_orderOf_eq_one σ
      have e : (⟨⟨Equiv.Perm.ofSubtype σ, h⟩, hst σ h⟩ :
          MulAction.stabilizer (alternatingGroup α) p) ^ 3 = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [← map_pow, h3, map_one]
      rw [e, map_one]
    | one =>
      intro h
      have e : (⟨⟨Equiv.Perm.ofSubtype (1 : Equiv.Perm {x // x ≠ p}), h⟩, hst 1 h⟩ :
          MulAction.stabilizer (alternatingGroup α) p) = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      rw [e, map_one]
    | mul a b ha hb iha ihb =>
      intro h
      have ha' := hι a (by rwa [Equiv.Perm.closure_three_cycles_eq_alternating] at ha)
      have hb' := hι b (by rwa [Equiv.Perm.closure_three_cycles_eq_alternating] at hb)
      have e : (⟨⟨Equiv.Perm.ofSubtype (a * b), h⟩, hst (a * b) h⟩ :
          MulAction.stabilizer (alternatingGroup α) p) =
          ⟨⟨Equiv.Perm.ofSubtype a, ha'⟩, hst a ha'⟩ *
            ⟨⟨Equiv.Perm.ofSubtype b, hb'⟩, hst b hb'⟩ := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      rw [e, map_mul, iha ha', ihb hb', mul_one]
    | inv a ha iha =>
      intro h
      have ha' := hι a (by rwa [Equiv.Perm.closure_three_cycles_eq_alternating] at ha)
      have e : (⟨⟨Equiv.Perm.ofSubtype a⁻¹, h⟩, hst a⁻¹ h⟩ :
          MulAction.stabilizer (alternatingGroup α) p) =
          (⟨⟨Equiv.Perm.ofSubtype a, ha'⟩, hst a ha'⟩)⁻¹ := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      rw [e, map_inv, iha ha']
      exact inv_one
  refine MonoidHom.ext fun h => ?_
  obtain ⟨⟨σ, hσ⟩, hσp⟩ := h
  have hσp' : σ p = p := MulAction.mem_stabilizer_iff.mp hσp
  have h₁ : ∀ x, σ x ≠ p ↔ x ≠ p := fun x => by
    constructor
    · intro h hx
      exact h (hx ▸ hσp')
    · intro h hx
      exact h (σ.injective (hx.trans hσp'.symm))
  have h₂ : ∀ x, σ x ≠ x → x ≠ p := fun x hx hxp => hx (hxp ▸ hσp')
  have hτ : σ.subtypePerm h₁ ∈ alternatingGroup {x // x ≠ p} := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_subtypePerm σ h₁ h₂]
    exact hσ
  have he := Equiv.Perm.ofSubtype_subtypePerm h₁ h₂
  have hτ' := hι _ hτ
  have e : (⟨⟨σ, hσ⟩, hσp⟩ : MulAction.stabilizer (alternatingGroup α) p) =
      ⟨⟨Equiv.Perm.ofSubtype (σ.subtypePerm h₁), hτ'⟩, hst _ hτ'⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    exact he.symm
  rw [e, key _ (by rwa [Equiv.Perm.closure_three_cycles_eq_alternating])]
  rfl

theorem exists_coboundary_alternatingGroup (h3 : 3 ≤ Nat.card α)
    (c : alternatingGroup α → α → ZMod 2) (hc : ∀ g h y, c (g * h) y = c g y + c h (g⁻¹ • y)) :
    ∃ e : α → ZMod 2, ∀ g y, c g y = e (g⁻¹ • y) + e y := by
  have := alternatingGroup.isPretransitive_of_three_le_card α h3
  have hne : Nonempty α := by
    rw [← Nat.card_pos_iff.trans (and_iff_left inferInstance)]
    omega
  obtain ⟨x₀⟩ := hne
  exact exists_coboundary_of_pretransitive x₀ (alternatingGroup_stabilizer_hom_eq_one x₀) c hc

end Alternating

end CFSG.Quasithin.H13.Lem26A8
