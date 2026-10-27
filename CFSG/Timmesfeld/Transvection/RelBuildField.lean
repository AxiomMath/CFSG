module

public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

public section

namespace CFSG.Timmesfeld.Transvection.RelBuild

variable {F : Type*} [Field F] (σ : F ≃+* F)

@[expose] def tw : Bool → F → F
  | true, s => σ s
  | false, s => s

@[simp] theorem tw_true (s : F) : tw σ true s = σ s := rfl

@[simp] theorem tw_false (s : F) : tw σ false s = s := rfl

theorem tw_mul (e : Bool) (s t : F) : tw σ e (s * t) = tw σ e s * tw σ e t := by
  cases e <;> simp

theorem tw_add (e : Bool) (s t : F) : tw σ e (s + t) = tw σ e s + tw σ e t := by
  cases e <;> simp

@[simp] theorem tw_one (e : Bool) : tw σ e 1 = 1 := by
  cases e <;> simp

@[simp] theorem tw_zero (e : Bool) : tw σ e 0 = 0 := by
  cases e <;> simp

theorem tw_fixed (e : Bool) {c : F} (hc : σ c = c) : tw σ e c = c := by
  cases e <;> simp [hc]

variable {σ}

theorem tw_tw (hσ : ∀ c, σ (σ c) = c) (e₁ e₂ : Bool) (s : F) :
    tw σ e₁ (tw σ e₂ s) = tw σ (xor e₁ e₂) s := by
  cases e₁ <;> cases e₂ <;> simp [hσ]

theorem tw_tw_self (hσ : ∀ c, σ (σ c) = c) (e : Bool) (s : F) : tw σ e (tw σ e s) = s := by
  cases e <;> simp [hσ]

theorem σ_tw (e : Bool) (s : F) : σ (tw σ e s) = tw σ e (σ s) := by
  cases e <;> simp

theorem norm_tw (hσ : ∀ c, σ (σ c) = c) (e : Bool) (s : F) :
    σ (tw σ e s) * tw σ e s = σ s * s := by
  cases e
  · simp
  · simp [hσ, mul_comm]

theorem tw_smul (e : Bool) {c : F} (hc : σ c = c) (s : F) : tw σ e (c * s) = c * tw σ e s := by
  rw [tw_mul, tw_fixed σ e hc]

theorem eq_of_tw_eq (hne : ∃ θ, σ θ ≠ θ) {e₁ e₂ : Bool} (h : ∀ s, tw σ e₁ s = tw σ e₂ s) :
    e₁ = e₂ := by
  obtain ⟨θ, hθ⟩ := hne
  have h' := h θ
  cases e₁ <;> cases e₂ <;> simp only [tw_false, tw_true] at h'
  · rfl
  · exact absurd h'.symm hθ
  · exact absurd h' hθ
  · rfl

variable [CharP F 2]

theorem trace_ne_zero {θ : F} (hθ : σ θ ≠ θ) : θ + σ θ ≠ 0 := fun h =>
  hθ (CharTwo.add_eq_zero.1 h).symm

omit [CharP F 2] in
theorem exists_fixed_add_mul (hσ : ∀ c, σ (σ c) = c) {θ : F} (hθ : σ θ ≠ θ) (z : F) :
    ∃ a b, σ a = a ∧ σ b = b ∧ a + b * θ = z := by
  have hδ : θ - σ θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have hb : σ ((z - σ z) / (θ - σ θ)) = (z - σ z) / (θ - σ θ) := by
    rw [map_div₀, map_sub, map_sub, hσ, hσ, ← neg_sub z, ← neg_sub θ, neg_div_neg_eq]
  refine ⟨z - (z - σ z) / (θ - σ θ) * θ, (z - σ z) / (θ - σ θ), ?_, hb, by ring⟩
  rw [map_sub, map_mul, hb]
  field_simp
  ring

theorem eq_zero_of_trace_mul (hne : ∃ θ, σ θ ≠ θ) {κ : F} (h : ∀ x, κ * x + σ (κ * x) = 0) :
    κ = 0 := by
  by_contra hκ
  obtain ⟨θ, hθ⟩ := hne
  have := h (θ / κ)
  rw [mul_div_cancel₀ θ hκ] at this
  exact trace_ne_zero hθ this

theorem exists_sq_eq [Finite F] (x : F) : ∃ s, s ^ 2 = x := by
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' x
  exact ⟨s, by rw [hs, sq]⟩

theorem similitude [Finite F] (hσ : ∀ c, σ (σ c) = c) (hne : ∃ θ, σ θ ≠ θ) {φ : F → F}
    (hadd : ∀ s t, φ (s + t) = φ s + φ t) (hsmul : ∀ c s, σ c = c → φ (c * s) = c * φ s)
    {m : F} (hN : ∀ s, σ (φ s) * φ s = m * (σ s * s)) :
    (∀ s, φ s = φ 1 * s) ∨ (∀ s, φ s = φ 1 * σ s) := by
  obtain ⟨θ, hθ⟩ := hne
  have hδ : σ θ - θ ≠ 0 := sub_ne_zero.2 hθ
  obtain ⟨l', hl'⟩ : ∃ l', l' = (φ θ - φ 1 * θ) / (σ θ - θ) := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = φ 1 - l' := ⟨_, rfl⟩
  have hrep : ∀ s, φ s = l * s + l' * σ s := by
    intro s
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_fixed_add_mul hσ hθ s
    have h1 : φ a = a * φ 1 := by rw [← hsmul a 1 ha, mul_one]
    rw [hadd, h1, hsmul b θ hb, map_add, map_mul, ha, hb, hl, hl']
    field_simp
    ring
  have key : ∀ s, l * σ l' * s ^ 2 + σ (l * σ l' * s ^ 2) =
      (m - (σ l * l + σ l' * l')) * (σ s * s) := by
    intro s
    have h := hN s
    rw [hrep s] at h
    simp only [map_add, map_mul, map_pow, hσ] at h ⊢
    linear_combination h
  have hm : m - (σ l * l + σ l' * l') = 0 := by
    have h1 := key 1
    have h2 := key (θ + 1)
    have h3 := key θ
    rw [CharTwo.add_sq, one_pow] at h2
    have h4 : (m - (σ l * l + σ l' * l')) * (θ + σ θ) = 0 := by
      simp only [one_pow, mul_one, map_one, map_add, map_mul, map_pow] at h1 h2 h3
      linear_combination h1 + h3 - h2
    exact (mul_eq_zero.1 h4).resolve_right (trace_ne_zero hθ)
  have hκ : l * σ l' = 0 := by
    refine eq_zero_of_trace_mul ⟨θ, hθ⟩ fun x => ?_
    obtain ⟨s, rfl⟩ := exists_sq_eq x
    rw [key s, hm, zero_mul]
  rcases mul_eq_zero.1 hκ with h | h
  · right
    intro s
    have h1 : φ 1 = l' := by rw [hrep, h, map_one]; ring
    rw [hrep, h, h1]
    ring
  · left
    have h' : l' = 0 := by rwa [map_eq_zero] at h
    intro s
    have h1 : φ 1 = l := by rw [hrep, h', map_one]; ring
    rw [hrep, h', h1]
    ring

theorem forall_or_forall_of_add {P Q : F → Prop} (hP : ∀ a b, P a → P b → P (a + b))
    (hQ : ∀ a b, Q a → Q b → Q (a + b)) (h : ∀ t, P t ∨ Q t) : (∀ t, P t) ∨ (∀ t, Q t) := by
  by_contra hc
  rw [not_or, not_forall, not_forall] at hc
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hc
  have hQa : Q a := (h a).resolve_left ha
  have hPb : P b := (h b).resolve_right hb
  rcases h (a + b) with hab | hab
  · apply ha
    have := hP _ _ hab hPb
    rwa [add_assoc, CharTwo.add_self_eq_zero, add_zero] at this
  · apply hb
    have := hQ _ _ hab hQa
    rwa [add_comm a b, add_assoc, CharTwo.add_self_eq_zero, add_zero] at this

theorem exists_normal_form [Finite F] (hσ : ∀ c, σ (σ c) = c) (hne : ∃ θ, σ θ ≠ θ)
    {μ : F → F → F} (hadd₁ : ∀ s s' t, μ (s + s') t = μ s t + μ s' t)
    (hadd₂ : ∀ s t t', μ s (t + t') = μ s t + μ s t')
    (hsmul₁ : ∀ c s t, σ c = c → μ (c * s) t = c * μ s t)
    (hsmul₂ : ∀ c s t, σ c = c → μ s (c * t) = c * μ s t)
    (hN : ∀ s t, σ (μ s t) * μ s t = σ s * s * (σ t * t)) :
    ∃ c e₁ e₂, σ c * c = 1 ∧ ∀ s t, μ s t = c * tw σ e₁ s * tw σ e₂ t := by
  have hcol : ∀ t, (∀ s, μ s t = μ 1 t * s) ∨ (∀ s, μ s t = μ 1 t * σ s) := fun t =>
    similitude hσ hne (fun s s' => hadd₁ s s' t) (fun c s hc => hsmul₁ c s t hc)
      (m := σ t * t) (fun s => by rw [hN]; ring)
  have hrow : ∀ s, (∀ t, μ s t = μ s 1 * t) ∨ (∀ t, μ s t = μ s 1 * σ t) := fun s =>
    similitude hσ hne (fun t t' => hadd₂ s t t') (fun c t hc => hsmul₂ c s t hc)
      (m := σ s * s) (fun t => hN s t)
  obtain ⟨e₁, he₁⟩ : ∃ e₁, ∀ s t, μ s t = μ 1 t * tw σ e₁ s := by
    rcases forall_or_forall_of_add (P := fun t => ∀ s, μ s t = μ 1 t * s)
      (Q := fun t => ∀ s, μ s t = μ 1 t * σ s)
      (fun a b ha hb s => by rw [hadd₂, hadd₂, ha, hb]; ring)
      (fun a b ha hb s => by rw [hadd₂, hadd₂, ha, hb]; ring) hcol with h | h
    · exact ⟨false, fun s t => h t s⟩
    · exact ⟨true, fun s t => h t s⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂, ∀ s t, μ s t = μ s 1 * tw σ e₂ t := by
    rcases forall_or_forall_of_add (P := fun s => ∀ t, μ s t = μ s 1 * t)
      (Q := fun s => ∀ t, μ s t = μ s 1 * σ t)
      (fun a b ha hb t => by rw [hadd₁, hadd₁, ha, hb]; ring)
      (fun a b ha hb t => by rw [hadd₁, hadd₁, ha, hb]; ring) hrow with h | h
    · exact ⟨false, fun s t => h s t⟩
    · exact ⟨true, fun s t => h s t⟩
  refine ⟨μ 1 1, e₁, e₂, by simpa using hN 1 1, fun s t => ?_⟩
  rw [he₁ s t, he₂ 1 t]
  ring

end CFSG.Timmesfeld.Transvection.RelBuild
