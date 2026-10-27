module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType

namespace RootDetectTwE6

variable {K : Type*} [Field K]

theorem cases_of_cubic_on (F : Subfield K) (δ : K →* K) {d e₁ e₂ e₃ : K} (hd : d ≠ 0)
    (h : ∀ t ∈ F, d * δ t = e₁ * t + e₂ * t ^ 2 + e₃ * t ^ 3) :
    (∀ t ∈ F, δ t = t) ∨ (∀ t ∈ F, δ t = t ^ 2) ∨ (∀ t ∈ F, δ t = t ^ 3) := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨⟨t₁, ht₁F, ht₁⟩, ⟨t₂, ht₂F, ht₂⟩, ⟨t₃, ht₃F, ht₃⟩⟩ := hne
  have hli := linearIndependent_monoidHom F K
  let ι : F →* K := F.subtype.toMonoidHom
  let χ : F →* K := δ.comp ι
  let χ₂ : F →* K := (powMonoidHom 2).comp ι
  let χ₃ : F →* K := (powMonoidHom 3).comp ι
  have h1 : χ ≠ ι := fun e => ht₁ (DFunLike.congr_fun e ⟨t₁, ht₁F⟩)
  have h2 : χ ≠ χ₂ := fun e => ht₂ (DFunLike.congr_fun e ⟨t₂, ht₂F⟩)
  have h3 : χ ≠ χ₃ := fun e => ht₃ (DFunLike.congr_fun e ⟨t₃, ht₃F⟩)
  let l : (F →* K) →₀ K := Finsupp.single χ d - Finsupp.single ι e₁ -
    Finsupp.single χ₂ e₂ - Finsupp.single χ₃ e₃
  have hl : Finsupp.linearCombination K (fun f : F →* K => (f : F → K)) l = 0 := by
    simp only [l, map_sub, Finsupp.linearCombination_single]
    funext t
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    change d * δ t - e₁ * t - e₂ * (t : K) ^ 2 - e₃ * (t : K) ^ 3 = 0
    rw [h t t.2]
    ring
  have h0 := linearIndependent_iff.mp hli l hl
  have hχ := congrArg (fun m : (F →* K) →₀ K => m χ) h0
  simp only [l, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne h1, Finsupp.single_eq_of_ne h2, Finsupp.single_eq_of_ne h3,
    Finsupp.coe_zero, Pi.zero_apply, sub_zero] at hχ
  exact hd hχ

theorem exists_eq_pow_mul_pow (θ δ : K →* K) {d : K} (hd : d ≠ 0) (e : ℕ → ℕ → K)
    (h : ∀ t, d * δ t =
      ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4, e k l * (t ^ k * θ t ^ l)) :
    ∃ k < 4, ∃ l < 4, ∀ t, δ t = t ^ k * θ t ^ l := by
  classical
  by_contra hne
  push Not at hne
  have hli := linearIndependent_monoidHom K K
  let χ : ℕ → ℕ → (K →* K) := fun k l => powMonoidHom k * (powMonoidHom l).comp θ
  have hχ : ∀ k l t, χ k l t = t ^ k * θ t ^ l := fun _ _ _ => rfl
  have hne' : ∀ k ∈ Finset.range 4, ∀ l ∈ Finset.range 4, χ k l ≠ δ := by
    intro k hk l hl e
    obtain ⟨t, ht⟩ := hne k (Finset.mem_range.mp hk) l (Finset.mem_range.mp hl)
    exact ht (by rw [← hχ, e])
  let L : (K →* K) →₀ K := Finsupp.single δ d -
    ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4, Finsupp.single (χ k l) (e k l)
  have hL : Finsupp.linearCombination K (fun f : K →* K => (f : K → K)) L = 0 := by
    simp only [L, map_sub, map_sum, Finsupp.linearCombination_single]
    funext t
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hχ]
    rw [h t, sub_self]
  have h0 := linearIndependent_iff.mp hli L hL
  have hδ := congrArg (fun m : (K →* K) →₀ K => m δ) h0
  simp only [L, Finsupp.coe_sub, Finsupp.coe_finsetSum, Pi.sub_apply, Finset.sum_apply,
    Finsupp.single_eq_same, Finsupp.coe_zero, Pi.zero_apply] at hδ
  rw [Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl =>
    Finsupp.single_eq_of_ne (hne' k hk l hl).symm, sub_zero] at hδ
  exact hd hδ

theorem exists_eq_add_one [CharP K 2] (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c)
    (hne : ∃ b, θ b ≠ b) : ∃ s, θ s = s + 1 := by
  obtain ⟨b, hb⟩ := hne
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hw0 : b + θ b ≠ 0 := by
    intro h0
    apply hb
    linear_combination h0 - b * h2
  have hθw : θ (b + θ b) = b + θ b := by rw [map_add, hθ, add_comm]
  refine ⟨b / (b + θ b), ?_⟩
  rw [map_div₀, hθw, div_add_one hw0]
  congr 1
  linear_combination -b * h2

theorem fixed_or_sq_of_eq_pow_mul_pow [CharP K 2] (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c)
    (hne : ∃ b, θ b ≠ b) (δ : K →+* K) {k l : ℕ} (hk : k < 4) (hl : l < 4)
    (h : ∀ t, δ t = t ^ k * θ t ^ l) :
    (∀ c, θ c = c → δ c = c) ∨ (∀ c, θ c = c → δ c = c ^ 2) := by
  by_cases hF : ∀ a, θ a = a → a = 0 ∨ a = 1
  · left
    intro c hc
    rcases hF c hc with rfl | rfl
    · exact map_zero δ
    · exact map_one δ
  push Not at hF
  obtain ⟨a, ha, ha0, ha1⟩ := hF
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨s₀, hs₀⟩ := exists_eq_add_one θ hθ hne
  have hs₀a : θ (s₀ + a) = s₀ + a + 1 := by rw [map_add, hs₀, ha]; ring
  have key : ∀ s, θ s = s + 1 → (s + 1) ^ k * s ^ l = s ^ k * (s + 1) ^ l + 1 := by
    intro s hs
    have e1 := h (s + 1)
    rw [map_add, map_one, h s, map_add, map_one, hs] at e1
    have e2 : s + 1 + 1 = s := by linear_combination h2
    rw [e2] at e1
    exact e1.symm
  have bad₁ : ¬ ∀ s, θ s = s + 1 → (s ^ 2 + s + 1) ^ 2 = 0 := by
    intro hall
    have e1 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hall s₀ hs₀)
    have e2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hall (s₀ + a) hs₀a)
    have e3 : a * (a + 1) = 0 := by linear_combination e2 - e1 - s₀ * a * h2
    rcases mul_eq_zero.mp e3 with e | e
    · exact ha0 e
    · exact ha1 (by linear_combination e - h2)
  have bad₂ : s₀ ^ 2 + s₀ ≠ 0 := by
    intro e
    have e3 : s₀ * (s₀ + 1) = 0 := by linear_combination e
    rcases mul_eq_zero.mp e3 with e' | e'
    · rw [e', map_zero, zero_add] at hs₀
      exact zero_ne_one hs₀
    · have : s₀ = 1 := by linear_combination e' - h2
      rw [this, map_one] at hs₀
      exact one_ne_zero (by linear_combination hs₀ + h2 : (1 : K) = 0)
  have bad₃ : (1 : K) ≠ 0 := one_ne_zero
  interval_cases k <;> interval_cases l
  · exact absurd (by linear_combination key s₀ hs₀ + h2) bad₃
  · left; intro c hc; rw [h c, hc]; ring
  · right; intro c hc; rw [h c, hc]; ring
  · exact absurd (by linear_combination key s₀ hs₀ + (2 * s₀ ^ 2 + 2 * s₀ + 1) * h2) bad₂
  · left; intro c _; rw [h c]; ring
  · exact absurd (by linear_combination key s₀ hs₀ + h2) bad₃
  · exact absurd (fun s hs => by
      linear_combination (s ^ 2 + s + 1) * key s hs +
        (s ^ 4 + 2 * s ^ 3 + 3 * s ^ 2 + 2 * s + 1) * h2) bad₁
  · exact absurd (fun s hs => by
      linear_combination (s ^ 2 + s + 1) * key s hs +
        (s ^ 5 + 3 * s ^ 4 + 4 * s ^ 3 + 4 * s ^ 2 + 2 * s + 1) * h2) bad₁
  · right; intro c _; rw [h c]; ring
  · exact absurd (fun s hs => by
      linear_combination (s ^ 2 + s + 1) * key s hs + (s ^ 2 + s + 1) * h2) bad₁
  · exact absurd (by linear_combination key s₀ hs₀ + h2) bad₃
  · exact absurd (fun s hs => by
      linear_combination key s hs + (s ^ 4 + 2 * s ^ 3 + 2 * s ^ 2 + s + 1) * h2) bad₁
  · exact absurd (by linear_combination key s₀ hs₀ + (-s₀ ^ 2 - s₀) * h2) bad₂
  · exact absurd (fun s hs => by
      linear_combination (s ^ 2 + s + 1) * key s hs +
        (-s ^ 5 - 2 * s ^ 4 - 2 * s ^ 3 + s + 1) * h2) bad₁
  · exact absurd (fun s hs => by
      linear_combination key s hs + (s ^ 2 + s + 1) * h2) bad₁
  · exact absurd (by linear_combination key s₀ hs₀ + h2) bad₃

theorem eq_one_of_fixed_of_pow_eq_one (θ : K →+* K) (hθ : ∀ x, θ (θ x) = x) {φ : K ≃+* K}
    (hcomm : ∀ x, φ (θ x) = θ (φ x)) (hfix : ∀ x, θ x = x → φ x = x) {p : ℕ} (hp : Odd p)
    (hφp : φ ^ p = 1) : φ = 1 := by
  have hsq : φ * φ = 1 := by
    refine RingEquiv.ext fun x => ?_
    change φ (φ x) = x
    have hs : φ (x + θ x) = x + θ x := hfix _ (by rw [map_add, hθ, add_comm])
    have hm : φ (x * θ x) = x * θ x := hfix _ (by rw [map_mul, hθ, mul_comm])
    have e : φ x * φ x - φ (x + θ x) * φ x + φ (x * θ x) = 0 := by
      rw [← map_mul, ← map_mul, ← map_sub, ← map_add]
      have h0 : x * x - (x + θ x) * x + x * θ x = 0 := by ring
      rw [h0, map_zero]
    rw [hs, hm] at e
    have hroot : (φ x - x) * (φ x - θ x) = 0 := by linear_combination e
    rcases mul_eq_zero.mp hroot with h | h
    · have hx : φ x = x := sub_eq_zero.mp h
      rw [hx, hx]
    · have hx : φ x = θ x := sub_eq_zero.mp h
      rw [hx, hcomm, hx, hθ]
  obtain ⟨k, rfl⟩ := hp
  have hpow : φ ^ (2 * k + 1) = φ := by
    rw [pow_succ, pow_mul, sq, hsq, one_pow, one_mul]
  rw [← hpow, hφp]

theorem eq_one_of_fixed_or_sq (θ : K →+* K) (hθ : ∀ x, θ (θ x) = x) {δ : K ≃+* K}
    (hcomm : ∀ x, δ (θ x) = θ (δ x)) {p : ℕ} (hp : Odd p) (hδp : δ ^ p = 1)
    (h1 : (∀ c, θ c = c → δ c = c) ∨ (∀ c, θ c = c → δ c = c ^ 2))
    (h2 : (∀ c, θ c = c → δ⁻¹ c = c) ∨ (∀ c, θ c = c → δ⁻¹ c = c ^ 2)) : δ = 1 := by
  have hcomm' : ∀ x, δ⁻¹ (θ x) = θ (δ⁻¹ x) := by
    intro x
    apply δ.injective
    change δ (δ.symm (θ x)) = δ (θ (δ.symm x))
    rw [RingEquiv.apply_symm_apply, hcomm, RingEquiv.apply_symm_apply]
  have hinvp : δ⁻¹ ^ p = 1 := by rw [inv_pow, hδp, inv_one]
  rcases h1 with h1 | h1
  · exact eq_one_of_fixed_of_pow_eq_one θ hθ hcomm h1 hp hδp
  rcases h2 with h2 | h2
  · exact inv_eq_one.mp (eq_one_of_fixed_of_pow_eq_one θ hθ hcomm' h2 hp hinvp)
  have hsq : ∀ c, θ c = c → θ (c ^ 2) = c ^ 2 := fun c hc => by rw [map_pow, hc]
  have h4 : ∀ c, θ c = c → c ^ 4 = c := by
    intro c hc
    have e : δ⁻¹ (δ c) = c := by
      change δ.symm (δ c) = c
      exact δ.symm_apply_apply c
    rw [h1 c hc, h2 _ (hsq c hc)] at e
    calc c ^ 4 = (c ^ 2) ^ 2 := by ring
      _ = c := e
  have hδ2 : δ ^ 2 = 1 := by
    have hfix2 : ∀ c, θ c = c → (δ ^ 2) c = c := by
      intro c hc
      change δ (δ c) = c
      rw [h1 c hc, h1 _ (hsq c hc)]
      calc (c ^ 2) ^ 2 = c ^ 4 := by ring
        _ = c := h4 c hc
    have hcomm2 : ∀ x, (δ ^ 2) (θ x) = θ ((δ ^ 2) x) := by
      intro x
      change δ (δ (θ x)) = θ (δ (δ x))
      rw [hcomm, hcomm]
    refine eq_one_of_fixed_of_pow_eq_one θ hθ hcomm2 hfix2 hp ?_
    rw [← pow_mul, mul_comm, pow_mul, hδp, one_pow]
  obtain ⟨m, rfl⟩ := hp
  rw [pow_succ, pow_mul, hδ2, one_pow, one_mul] at hδp
  exact hδp

end RootDetectTwE6

end CFSG.StandardType
