module

public import CFSG.Quasithin.Background.SzG11NCGalois
public import CFSG.Quasithin.Background.SzG11NCSchur
public import CFSG.Quasithin.Background.P5FixedLinear

public section

namespace CFSG.Quasithin.SzG11NC

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def Three (X : Subgroup (GLV V)) (v₁ : V) : Prop :=
  (∀ v : V, (∀ x ∈ X, x v = v) → v = 0 ∨ v = v₁) ∨
    ∃ a ∈ X, Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2 ∧
      v₁ ∈ LinearMap.range (a.toLinearMap - LinearMap.id)

theorem not_three_of_field [Finite V] (E : Type) [Field E] [Finite E] [Module E V]
    (hE : 8 ≤ Nat.card E) (hd : 6 ≤ Module.finrank (ZMod 2) V)
    (X : Subgroup (GLV V)) (hX : ∀ x ∈ X, x * x = 1)
    (hsl : ∀ x ∈ X, ∃ σ : E ≃+* E, ∀ (e : E) (v : V), x (e • v) = σ e • x v)
    (v₁ : V) (hv₁ : v₁ ≠ 0) : ¬ Three X v₁ := by
  classical
  have hVne : Nontrivial V := by
    refine Module.nontrivial_of_finrank_pos (R := ZMod 2) ?_
    omega
  have hchar : CharP E 2 := by
    refine CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ?_
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply smul_left_inj_of_ne_zero hv
    rw [two_smul, zmod_two_add_self, zero_smul]
  choose! σ hσ using hsl
  have hσσ : ∀ x ∈ X, ∀ e, σ x (σ x e) = e := by
    intro x hx e
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hxx : ∀ w, x (x w) = w := fun w => by
      simpa using congrArg (fun g : GLV V => g w) (hX x hx)
    have h5 : x (x (e • v)) = σ x (σ x e) • v := by
      rw [hσ x hx, hσ x hx, hxx]
    have h6 : x (x (e • v)) = e • v := hxx _
    exact smul_left_inj_of_ne_zero hv (h5.symm.trans h6)
  obtain ⟨κ₀, hκ0, hκ1, hκfix⟩ := exists_common_fix hE {τ | ∃ x ∈ X, τ = σ x}
    (by rintro τ ⟨x, hx, rfl⟩ e; exact hσσ x hx e)
  have hfixκ : ∀ x ∈ X, σ x κ₀ = κ₀ := fun x hx => hκfix _ ⟨x, hx, rfl⟩
  have hVcard : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rwa [Nat.card_zmod] at this
  rintro (h | ⟨a, haX, hrk, hv⟩)
  ·
    have h2V : 2 ∣ Nat.card V := by
      rw [hVcard]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨u, hu0, hu⟩ := CFSG.Quasithin.G11.P5.exists_fixed_ne_zero X hX h2V
    have hu' : ∀ x ∈ X, x (κ₀ • u) = κ₀ • u := by
      intro x hx
      rw [hσ x hx, hfixκ x hx, hu x hx]
    have hu'0 : κ₀ • u ≠ 0 := smul_ne_zero hκ0 hu0
    have e1 := h u hu
    have e2 := h (κ₀ • u) hu'
    rcases e1 with e1 | e1
    · exact hu0 e1
    rcases e2 with e2 | e2
    · exact hu'0 e2
    have : κ₀ • u = (1 : E) • u := by rw [one_smul, e2, e1]
    exact hκ1 (smul_left_inj_of_ne_zero hu0 this)
  · by_cases hlin : ∀ e, σ a e = e
    ·
      have hRsmul : ∀ (e : E), v₁ ∈ LinearMap.range (a.toLinearMap - LinearMap.id) →
          e • v₁ ∈ LinearMap.range (a.toLinearMap - LinearMap.id) := by
        rintro e ⟨w, hw⟩
        refine ⟨e • w, ?_⟩
        simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at hw ⊢
        rw [hσ a haX, hlin e, ← smul_sub, hw]
      let f : E → LinearMap.range (a.toLinearMap - LinearMap.id) :=
        fun e => ⟨e • v₁, hRsmul e hv⟩
      have hf : Function.Injective f := by
        intro e e' h
        exact smul_left_inj_of_ne_zero hv₁ (congrArg Subtype.val h)
      have hcard : Nat.card E ≤ Nat.card (LinearMap.range (a.toLinearMap - LinearMap.id)) :=
        Nat.card_le_card_of_injective f hf
      have hRcard : Nat.card (LinearMap.range (a.toLinearMap - LinearMap.id)) =
          2 ^ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) := by
        have := Module.natCard_eq_pow_finrank (K := ZMod 2)
          (V := LinearMap.range (a.toLinearMap - LinearMap.id))
        rwa [Nat.card_zmod] at this
      rw [hRcard] at hcard
      have : 2 ^ 3 ≤
          2 ^ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) := by
        calc 2 ^ 3 = 8 := by norm_num
          _ ≤ _ := le_trans hE hcard
      have := (Nat.pow_le_pow_iff_right (by norm_num)).1 this
      omega
    ·
      push Not at hlin
      obtain ⟨θ, hθ⟩ := exists_theta (σ a) (hσσ a haX) hlin
      have haa : ∀ v, a (a v) = v := by
        intro v
        have := hX a haX
        simpa using congrArg (fun g : GLV V => g v) this
      have hker : LinearMap.range (a.toLinearMap - LinearMap.id) =
          LinearMap.ker (a.toLinearMap - LinearMap.id) := by
        apply le_antisymm
        · rintro _ ⟨w, rfl⟩
          rw [LinearMap.mem_ker]
          simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
          have : a (a w - w) - (a w - w) = (w + w) - (a w + a w) := by
            rw [map_sub, haa]; abel
          rw [this, zmod_two_add_self, zmod_two_add_self, sub_zero]
        · intro v hv'
          rw [LinearMap.mem_ker] at hv'
          have hav : a v = v := by
            simpa [sub_eq_zero] using hv'
          refine ⟨θ • v, ?_⟩
          simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
          rw [hσ a haX, hav, ← sub_smul]
          have : σ a θ - θ = 1 := by
            have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
            linear_combination hθ - θ * h2
          rw [this, one_smul]
      have hrn := LinearMap.finrank_range_add_finrank_ker (a.toLinearMap - LinearMap.id)
      rw [← hker] at hrn
      omega

theorem not_three_of_scalars [Finite V] (H Γ : Subgroup (GLV V)) (hirr : IsIrr H ⊤)
    (hnorm : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (K : Type) [Field K] [Finite K] (hK : 8 ≤ Nat.card K)
    (hd : 6 ≤ Module.finrank (ZMod 2) V) (sc : K →+* Module.End (ZMod 2) V)
    (hsc : ∀ κ, ∀ h ∈ H, ∀ v, sc κ (h v) = h (sc κ v))
    (X : Subgroup (GLV V)) (hXΓ : X ≤ Γ) (hX : ∀ x ∈ X, x * x = 1) (v₁ : V) (hv₁ : v₁ ≠ 0) :
    ¬ Three X v₁ :=
  not_three_of_field (CommF H hirr) (le_trans hK (CommF.card_le K sc hsc)) hd X hX
    (fun _ hx => CommF.exists_semilinear Γ hnorm (hXΓ hx)) v₁ hv₁

end CFSG.Quasithin.SzG11NC
