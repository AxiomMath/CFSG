module

public import CFSG.Quasithin.Background.SmithB42D4Gen

public section

namespace CFSG.Quasithin.B42D4

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

section Lambda

variable {K : Type} [Field K] [CharP K 2]

local notation "Xr" => pinnedX TwistTag.D4.tag K

variable (K) in
@[expose] noncomputable def lam (e f : K) : ModGL TwistTag.D4.tag K := Xr d4P e * Xr d4H f

theorem lam_mul (e f e' f' : K) : lam K e f * lam K e' f' = lam K (e + e') (f + f') := by
  have hc := (commute_of_d4CommB (K := K) (α := d4H) (β := d4P) (by decide +kernel) f e').eq
  simp only [lam]
  rw [pinnedX_add, pinnedX_add, mul_assoc, ← mul_assoc (Xr d4H f), hc]
  group

theorem lam_mul_self (e f : K) : lam K e f * lam K e f = 1 := by
  rw [lam_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
  simp [lam, pinnedX_zero]

theorem lam_inv (e f : K) : (lam K e f)⁻¹ = lam K e f :=
  inv_eq_of_mul_eq_one_right (lam_mul_self e f)

theorem lam_comm (e f e' f' : K) : lam K e f * lam K e' f' = lam K e' f' * lam K e f := by
  rw [lam_mul, lam_mul, add_comm e, add_comm f]

theorem conjC_lam (γ e f : K) : Xr d4C γ * lam K e f * (Xr d4C γ)⁻¹ = lam K e (f + e * γ) := by
  have hCH : Commute (Xr d4C γ) (Xr d4H f) := commute_of_d4CommB (by decide +kernel) _ _
  have e1 : Xr d4C γ * Xr d4P e * (Xr d4C γ)⁻¹ = Xr d4P e * Xr d4H (e * γ) := by
    have h := rel_P_C (K := K) e γ
    rw [Xr_inv]
    calc Xr d4C γ * Xr d4P e * Xr d4C γ = Xr d4C γ * (Xr d4P e * Xr d4C γ) := by group
      _ = Xr d4C γ * (Xr d4C γ * Xr d4P e * Xr d4H (e * γ)) := by rw [h]
      _ = (Xr d4C γ * Xr d4C γ) * Xr d4P e * Xr d4H (e * γ) := by group
      _ = _ := by rw [Xr_mul_self, one_mul]
  simp only [lam]
  rw [conj_mul2, e1, hCH.eq, mul_inv_cancel_right, mul_assoc, ← pinnedX_add, add_comm (e * γ)]

theorem conjNC_lam (γ e f : K) :
    Xr (-d4C) γ * lam K e f * (Xr (-d4C) γ)⁻¹ = lam K (e + γ * f) f := by
  have hNP : Commute (Xr (-d4C) γ) (Xr d4P e) := commute_of_d4CommB (by decide +kernel) _ _
  have e1 := conj_pinnedX_of_sum (K := K) (α := -d4C) (β := d4H) (γ := d4P) (by decide +kernel)
    γ f
  simp only [lam]
  rw [conj_mul2, hNP.eq, mul_inv_cancel_right, e1, ← mul_assoc, ← pinnedX_add]

theorem conj3_lam (γ γ' γ'' e f : K) :
    (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'') * lam K e f *
        (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'')⁻¹ =
      lam K (e + γ' * (f + e * γ'')) (f + e * γ'' + (e + γ' * (f + e * γ'')) * γ) := by
  calc (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'') * lam K e f *
        (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'')⁻¹ =
      Xr d4C γ * (Xr (-d4C) γ' * (Xr d4C γ'' * lam K e f * (Xr d4C γ'')⁻¹) *
        (Xr (-d4C) γ')⁻¹) * (Xr d4C γ)⁻¹ := by group
    _ = _ := by rw [conjC_lam, conjNC_lam, conjC_lam]

theorem lam_closure {σ : K ≃+* K} {e f : K} (he : σ e = e) (hf : σ f = f) (hne : e ≠ 0 ∨ f ≠ 0)
    {S : Subgroup (ModGL TwistTag.D4.tag K)}
    (hS : ∀ γ γ' γ'' : K, σ γ = γ → σ γ' = γ' → σ γ'' = γ'' →
      (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'') * lam K e f *
        (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'')⁻¹ ∈ S)
    {e' f' : K} (he' : σ e' = e') (hf' : σ f' = f') : lam K e' f' ∈ S := by
  have hfix : ∀ {x y : K}, σ x = x → σ y = y → σ (x / y) = x / y := fun hx hy => by
    rw [map_div₀, hx, hy]
  have hl : ∀ γ γ' γ'' : K, σ γ = γ → σ γ' = γ' → σ γ'' = γ'' →
      lam K (e + γ' * (f + e * γ'')) (f + e * γ'' + (e + γ' * (f + e * γ'')) * γ) ∈ S :=
    fun γ γ' γ'' h1 h2 h3 => by rw [← conj3_lam]; exact hS γ γ' γ'' h1 h2 h3
  have hsplit : lam K e' f' = lam K e' 0 * lam K 0 f' := by rw [lam_mul, add_zero, zero_add]
  rw [hsplit]
  by_cases he0 : e = 0
  ·
    subst he0
    have hf0 : f ≠ 0 := hne.resolve_left (not_not.2 rfl)
    have h5 : ∀ x : K, σ x = x → lam K x 0 ∈ S := by
      intro x hx
      have h1 := hl 0 (x / f) 0 (map_zero σ) (hfix hx hf) (map_zero σ)
      have h2 := hl 0 0 0 (map_zero σ) (map_zero σ) (map_zero σ)
      simp only [zero_mul, add_zero, mul_zero, zero_add] at h1 h2
      have := mul_mem h1 (inv_mem h2)
      rwa [lam_inv, lam_mul, CharTwo.add_self_eq_zero, add_zero, div_mul_cancel₀ _ hf0] at this
    have hγ' : σ (1 / f) = 1 / f := hfix (map_one σ) hf
    have h1 := hl f' (1 / f) 0 hf' hγ' (map_zero σ)
    have h2 := hl 0 (1 / f) 0 (map_zero σ) hγ' (map_zero σ)
    simp only [add_zero, mul_zero, zero_add] at h1 h2
    have h3 := mul_mem h1 (inv_mem h2)
    rw [lam_inv, lam_mul, div_mul_cancel₀ _ hf0, CharTwo.add_self_eq_zero, one_mul,
      show f + f' + f = f' by ring2] at h3
    exact mul_mem (h5 e' he') h3
  ·
    have h6 : ∀ x : K, σ x = x → lam K 0 x ∈ S := by
      intro x hx
      have h1 := hl 0 0 (x / e) (map_zero σ) (map_zero σ) (hfix hx he)
      have h2 := hl 0 0 0 (map_zero σ) (map_zero σ) (map_zero σ)
      simp only [zero_mul, add_zero, mul_zero] at h1 h2
      have := mul_mem h1 (inv_mem h2)
      rwa [lam_inv, lam_mul, CharTwo.add_self_eq_zero, mul_div_cancel₀ _ he0,
        show f + x + f = x by ring2] at this
    have hγ'' : σ ((1 + f) / e) = (1 + f) / e := hfix (by rw [map_add, map_one, hf]) he
    have h1 := hl 0 e' ((1 + f) / e) (map_zero σ) he' hγ''
    have h2 := hl 0 0 ((1 + f) / e) (map_zero σ) (map_zero σ) hγ''
    simp only [mul_zero, add_zero, zero_mul] at h1 h2
    have h3 := mul_mem h1 (inv_mem h2)
    rw [lam_inv, lam_mul, mul_div_cancel₀ _ he0, show f + (1 + f) = 1 by ring2,
      CharTwo.add_self_eq_zero, mul_one, show e + e' + e = e' by ring2] at h3
    exact mul_mem h3 (h6 f' hf')

end Lambda

end CFSG.Quasithin.B42D4
