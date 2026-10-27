module

public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2FldB
public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2FldTorus

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat uElt uElt_mul antiUnipotentCenter minorAut)
open CFSG.Quasithin.SteinbergBS (upper_diag_ne_zero)

variable {k : Type} [Field k] [CharP k 2] [Finite k]

theorem exists_szCentre_of_twist {W : Subgroup (antiSp k)} (hWZ : W ≤ antiUnipotentCenter k)
    (hsp : SpansCenter W) {h : antiSp k} (hh : IsUpper h) {r : ℕ}
    (hσ : ∀ w ∈ W, (MulAut.conj h * minorAut k ^ (2 * r + 1)) w ∈ W) {c₀ b₀ : k} (hc₀ : c₀ ≠ 0)
    (hb₀ : b₀ ≠ 0) {s : ℕ}
    (hK : ∀ b c : k, uElt 0 b c 0 ∈ W → ∃ y : k, c = c₀ * y ∧ b = b₀ * y ^ 2 ^ s) :
    ∃ (F₀ : Subfield k) (a : ℕ), 1 ≤ a ∧ Nat.card F₀ = 2 ^ (2 * a + 1) ∧
      ∃ d : antiSp k, IsUpper d ∧ W ≤ (szCentre F₀ a).map (MulAut.conj d).toMonoidHom := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card k = 2 ^ n := by
    have := Fintype.ofFinite k
    obtain ⟨n, -, hn⟩ := FiniteField.card k 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  let Y : Set k := {y | uElt 0 (b₀ * y ^ 2 ^ s) (c₀ * y) 0 ∈ W}
  have hYK : ∀ b c : k, uElt 0 b c 0 ∈ W → ∃ y ∈ Y, c = c₀ * y ∧ b = b₀ * y ^ 2 ^ s := by
    intro b c hbc
    obtain ⟨y, hc, hb⟩ := hK b c hbc
    refine ⟨y, ?_, hc, hb⟩
    show uElt 0 (b₀ * y ^ 2 ^ s) (c₀ * y) 0 ∈ W
    rw [← hb, ← hc]
    exact hbc
  obtain ⟨hd0, hd1, -, -⟩ := upper_diag_ne_zero hh
  have htw : ∀ y ∈ Y, ∃ y' ∈ Y,
      c₀ * y' = glMat (h : GL (Fin 4) k) 0 0 ^ 2 * (b₀ * y ^ 2 ^ s) ^ 2 ^ (r + 1) ∧
        b₀ * y' ^ 2 ^ s = glMat (h : GL (Fin 4) k) 0 0 * glMat (h : GL (Fin 4) k) 1 1 *
          (c₀ * y) ^ 2 ^ r := by
    intro y hy
    have hσy := hσ _ hy
    rw [P6B.sigma_uElt_center hh r] at hσy
    obtain ⟨y', hy'Y, hc, hb⟩ := hYK _ _ hσy
    refine ⟨y', hy'Y, ?_, hb.symm⟩
    rw [← hc, show 2 ^ (r + 1) = 2 ^ r * 2 from pow_succ 2 r, pow_mul]
  obtain ⟨b₁, c₁, b₂, c₂, hz₁, hz₂, hb₁, hdet⟩ := P6B.exists_indep hWZ hsp
  have hz₃ : uElt 0 (b₁ + b₂) (c₁ + c₂) 0 ∈ W := by
    have h3 := W.mul_mem hz₁ hz₂
    have : uElt 0 b₁ c₁ 0 * uElt 0 b₂ c₂ 0 = (uElt 0 (b₁ + b₂) (c₁ + c₂) 0 : antiSp k) := by
      rw [uElt_mul]
      congr 1 <;> ring
    rwa [this] at h3
  obtain ⟨y₁, hy₁, hc₁, hb₁'⟩ := hYK _ _ hz₁
  obtain ⟨y₂, hy₂, hc₂, hb₂'⟩ := hYK _ _ hz₂
  obtain ⟨y₃, hy₃, hc₃, hb₃'⟩ := hYK _ _ hz₃
  have n₁ : y₁ ≠ 0 := by
    rintro rfl
    apply hb₁
    rw [hb₁', zero_pow (pow_ne_zero _ two_ne_zero), mul_zero]
  have n₂ : y₂ ≠ 0 := by
    rintro rfl
    apply hdet
    rw [hb₂', hc₂, zero_pow (pow_ne_zero _ two_ne_zero)]
    ring
  have n₃ : y₃ ≠ 0 := by
    rintro rfl
    apply hdet
    rw [zero_pow (pow_ne_zero _ two_ne_zero), mul_zero] at hb₃'
    rw [mul_zero] at hc₃
    linear_combination c₁ * hb₃' - b₁ * hc₃
  have d₁₂ : y₁ ≠ y₂ := by
    intro e
    apply hdet
    rw [hc₁, hb₁', hc₂, hb₂', e]
    ring
  have d₁₃ : y₁ ≠ y₃ := by
    intro e
    apply hdet
    have hb : b₂ = 0 := by
      have : b₁ + b₂ = b₁ := by rw [hb₃', hb₁', e]
      linear_combination this
    have hc : c₂ = 0 := by
      have : c₁ + c₂ = c₁ := by rw [hc₃, hc₁, e]
      linear_combination this
    rw [hb, hc]
    ring
  have d₂₃ : y₂ ≠ y₃ := by
    intro e
    apply hb₁
    have : b₁ + b₂ = b₂ := by rw [hb₃', hb₂', e]
    linear_combination this
  obtain ⟨a, F₀, ha1, hcard, hferm, hfrob, hcov⟩ :=
    twist_shape hn hc₀ hb₀ (pow_ne_zero 2 hd0) htw hy₁ hy₂ hy₃ n₁ n₂ n₃ d₁₂ d₁₃ d₂₃
  refine ⟨F₀, a, ha1, hcard, ?_⟩
  have hβ₀ : b₀ * y₁ ^ 2 ^ s ≠ 0 := mul_ne_zero hb₀ (pow_ne_zero _ n₁)
  have hβθ : (b₀ * y₁ ^ 2 ^ s) ^ 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ hβ₀
  refine exists_dSp_of_coset hWZ F₀ a (κ := c₀ * y₁ / (b₀ * y₁ ^ 2 ^ s) ^ 2 ^ (a + 1))
    (div_ne_zero (mul_ne_zero hc₀ n₁) hβθ) hβ₀ fun b c hbc => ?_
  obtain ⟨y, hyY, hc, hb⟩ := hYK b c hbc
  obtain ⟨f, hf, rfl⟩ := hcov y hyY
  have hb' : b = b₀ * y₁ ^ 2 ^ s * f ^ 2 ^ a := by
    rw [hb, mul_pow, hfrob f hf]
    ring
  refine ⟨⟨f ^ 2 ^ a, F₀.pow_mem hf _, hb'⟩, ?_⟩
  have h2 : (f ^ 2 ^ a) ^ 2 ^ (a + 1) = f := by
    rw [← pow_mul, ← pow_add, show a + (a + 1) = 2 * a + 1 by ring]
    exact hferm f hf
  have hb2 : b ^ 2 ^ (a + 1) = (b₀ * y₁ ^ 2 ^ s) ^ 2 ^ (a + 1) * f := by
    rw [hb', mul_pow (b₀ * y₁ ^ 2 ^ s) (f ^ 2 ^ a), h2]
  rw [hc, hb2]
  field_simp

end CFSG.Quasithin.Ch3E213M.Sp4C2
