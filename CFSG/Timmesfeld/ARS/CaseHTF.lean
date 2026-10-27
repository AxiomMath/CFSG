module

public import CFSG.Timmesfeld.ARS.CaseHIdent

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

variable {A A₀ P P' : Subgroup G}

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]

omit [CharP E 2] in
theorem N_zero : c.N 0 = 0 := by
  have := S.hyp.finite
  apply c.x2_injective (S.hyp.root.card_eq S.hA S.hP'.2.1)
  rw [c.x2_N, c.x2_zero]
  change ((S.proj ⟨_, c.comm1_mem 0⟩).2.2.2 : G) = 1
  have : (⟨_, c.comm1_mem 0⟩ : ↥(M R A)) = 1 :=
    Subtype.ext (by simp only [c.x1_zero, commutatorElement_one_left]; rfl)
  rw [this, map_one]
  rfl

theorem T_zero_left (r : E) : c.T 0 r = 0 := by
  have := S.hyp.finite
  apply c.x2_injective (S.hyp.root.card_eq S.hA S.hP'.2.1)
  rw [c.x2_T, c.x1_zero, commutatorElement_one_left, c.x2_zero]

omit [CharP E 2] in
theorem F2_zero_left (w : E) : c.F2 0 w = 0 := by
  have := S.hyp.finite
  apply c.x2_injective (S.hyp.root.card_eq S.hA S.hP'.2.1)
  rw [c.x2_F2, c.x2_zero]
  have : (⟨_, (c.comm15_mem 0 w).1⟩ : ↥(M R A)) = 1 :=
    Subtype.ext (by simp only [c.x1_zero, commutatorElement_one_left]; rfl)
  rw [this, map_one]
  rfl

variable [Finite F] [CharP F 2] [Finite E] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
  {τ : F} (hτ0 : τ ≠ 0) (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))
include he hτ0 hτ

omit [Finite E] in
theorem e_N (s : E) : e (τ⁻¹ * c.N s) = s * c.sharp s := by
  by_cases hs : s = 0
  · rw [hs, c.N_zero, c.sharp_zero, mul_zero, map_zero, zero_mul]
  · rw [c.N_eq hτ hs, ← mul_assoc, inv_mul_cancel₀ hτ0, one_mul, mul_comm s,
      c.sharp_mul_self_eq e he hτ0 hτ hs]

theorem G2_structure (hsq : ∀ s, c.sharp s = s ^ 2) :
    (∀ s, e (τ⁻¹ * c.N s) = s ^ 3) ∧ (∀ s w, c.F3 s w = 0) ∧
      (∀ s w, e (τ⁻¹ * c.F2 s w) = s ^ 2 * w) ∧ ∀ s r, e (τ⁻¹ * c.T s r) = s * r := by
  have hN : ∀ s, e (τ⁻¹ * c.N s) = s ^ 3 := fun s => by
    rw [c.e_N e he hτ0 hτ, hsq]
    ring
  have hF3 : ∀ s w, c.F3 s w = 0 := fun s w => by
    have h := c.polar_sharp e he s w
    rw [hsq, hsq, hsq, add_pow_char] at h
    linear_combination h.symm
  have hF2 : ∀ s w, e (τ⁻¹ * c.F2 s w) = s ^ 2 * w := fun s w => by
    by_cases hs : s = 0
    · rw [hs, c.F2_zero_left, mul_zero, map_zero]
      ring
    · obtain ⟨h1, -⟩ := c.weyl_U5 e he hτ0 hτ hs w
      rw [hF3, hsq, add_zero] at h1
      have h1' : e (τ⁻¹ * c.F2 s w) * s⁻¹ ^ 2 = w := by
        have := eq_neg_of_add_eq_zero_right h1
        rwa [CharTwo.neg_eq] at this
      calc e (τ⁻¹ * c.F2 s w) = e (τ⁻¹ * c.F2 s w) * s⁻¹ ^ 2 * s ^ 2 := by field_simp
        _ = s ^ 2 * w := by rw [h1', mul_comm]
  refine ⟨hN, hF3, hF2, fun s r => ?_⟩
  obtain ⟨w, rfl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq E 2) r
  have h := c.polar_N e he s w
  have h' := congrArg (fun x => e (τ⁻¹ * x)) h
  simp only [mul_add, map_add] at h'
  rw [hN, hN, hN, hF2, hsq] at h'
  rw [← sq]
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination (-1 : E) * h' + (s ^ 2 * w + s * w ^ 2) * h2

end Coords

section Sigma

variable {E : Type} [Field E] [CharP E 2] (σ : E →+* E) (hσ3 : ∀ x, σ (σ (σ x)) = x)
include hσ3

theorem eq_one_of_sigma {x : E} (hx : σ x * σ (σ x) = 1) : x = 1 := by
  have h2' : (2 : E) = 0 := CharTwo.two_eq_zero
  have h1 : σ (σ x) * x = 1 := by
    have := congrArg σ hx
    rwa [map_mul, hσ3, map_one] at this
  have hσx : σ x = x :=
    (eq_inv_of_mul_eq_one_left hx).trans (eq_inv_of_mul_eq_one_right h1).symm
  rw [hσx, hσx] at hx
  have h3 : (x + 1) * (x + 1) = 0 := by linear_combination hx + (x + 1) * h2'
  have h4 := mul_self_eq_zero.1 h3
  linear_combination h4 - h2'

@[expose] def trace3 (x : E) : E := x + σ x + σ (σ x)

omit [CharP E 2] in
theorem norm_add (s w : E) :
    (s + w) * σ (s + w) * σ (σ (s + w)) = w * σ w * σ (σ w) + s * σ s * σ (σ s) +
      trace3 σ (σ s * σ (σ s) * w) + trace3 σ (s * (σ w * σ (σ w))) := by
  simp only [trace3, map_add, map_mul, hσ3]
  ring

theorem solve_F2 {s : E} (hs : s ≠ 0) (w X : E)
    (h : w + (σ s⁻¹ * σ (σ (σ s * σ (σ w) + σ (σ s) * σ w)) +
        σ (σ s⁻¹) * σ (σ s * σ (σ w) + σ (σ s) * σ w)) + X * (σ s⁻¹ * σ (σ s⁻¹)) = 0) :
    X = trace3 σ (σ s * σ (σ s) * w) := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have ha : σ s ≠ 0 := (map_ne_zero σ).2 hs
  have hb : σ (σ s) ≠ 0 := (map_ne_zero σ).2 ha
  simp only [map_add, map_mul, map_inv₀, hσ3] at h
  simp only [trace3, map_mul, hσ3]
  have hX : X = σ s * σ (σ s) * (X * ((σ s)⁻¹ * (σ (σ s))⁻¹)) := by field_simp
  have h' : X * ((σ s)⁻¹ * (σ (σ s))⁻¹) = -(w + ((σ s)⁻¹ * (s * σ w + σ s * w) +
      (σ (σ s))⁻¹ * (σ (σ s) * w + s * σ (σ w)))) := by
    linear_combination h
  rw [hX, h']
  have e1 : σ s * (σ s)⁻¹ = 1 := mul_inv_cancel₀ ha
  have e2 : σ (σ s) * (σ (σ s))⁻¹ = 1 := mul_inv_cancel₀ hb
  linear_combination (-(σ (σ s) * s * σ w) - σ s * σ (σ s) * w) * e1 +
    (-(σ s * σ (σ s) * w) - σ s * s * σ (σ w)) * e2 +
    (-(2 * σ s * σ (σ s) * w) - σ (σ s) * s * σ w - σ s * s * σ (σ w)) * h2

end Sigma

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]
  [Finite F] [CharP F 2] [Finite E] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
  {τ : F} (hτ0 : τ ≠ 0) (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))
include he hτ0 hτ

theorem D4_structure (σ : E →+* E) (hσ3 : ∀ x, σ (σ (σ x)) = x)
    (hsq : ∀ s, c.sharp s = σ s * σ (σ s)) :
    (∀ s, e (τ⁻¹ * c.N s) = s * σ s * σ (σ s)) ∧
      (∀ s w, c.F3 s w = σ s * σ (σ w) + σ (σ s) * σ w) ∧
      (∀ s w, e (τ⁻¹ * c.F2 s w) = trace3 σ (c.sharp s * w)) ∧
      ∀ s r, e (τ⁻¹ * c.T s r) = trace3 σ (s * r) := by
  have hN : ∀ s, e (τ⁻¹ * c.N s) = s * σ s * σ (σ s) := fun s => by
    rw [c.e_N e he hτ0 hτ, hsq]
    ring
  have hF3 : ∀ s w, c.F3 s w = σ s * σ (σ w) + σ (σ s) * σ w := fun s w => by
    have h := c.polar_sharp e he s w
    rw [hsq, hsq, hsq] at h
    simp only [map_add] at h
    linear_combination h.symm
  have hF2 : ∀ s w, e (τ⁻¹ * c.F2 s w) = trace3 σ (c.sharp s * w) := fun s w => by
    by_cases hs : s = 0
    · rw [hs, c.F2_zero_left, mul_zero, map_zero, c.sharp_zero, zero_mul]
      simp [trace3]
    · obtain ⟨h1, -⟩ := c.weyl_U5 e he hτ0 hτ hs w
      rw [hF3, hF3, hsq] at h1
      rw [hsq]
      exact solve_F2 σ hσ3 hs w _ h1
  refine ⟨hN, hF3, hF2, fun s r => ?_⟩
  have hinj : Function.Injective c.sharp := by
    intro x y hxy
    by_cases hx : x = 0
    · rw [hx, c.sharp_zero] at hxy
      by_contra hne
      exact c.sharp_ne_zero e he hτ0 hτ (Ne.symm (hx ▸ hne)) hxy.symm
    by_cases hy : y = 0
    · rw [hy, c.sharp_zero] at hxy
      exact absurd hxy (c.sharp_ne_zero e he hτ0 hτ hx)
    have h1 : c.sharp (x / y) = 1 := by
      have := c.sharp_mul e he hτ0 hτ (x / y) y
      rw [div_mul_cancel₀ x hy, hxy] at this
      have hne := c.sharp_ne_zero e he hτ0 hτ hy
      exact mul_right_cancel₀ hne (this.symm.trans (one_mul _).symm)
    rw [hsq] at h1
    exact (div_eq_one_iff_eq hy).1 (eq_one_of_sigma σ hσ3 h1)
  obtain ⟨w, rfl⟩ := (Finite.injective_iff_surjective.1 hinj) r
  have h := c.polar_N e he s w
  have h' := congrArg (fun x => e (τ⁻¹ * x)) h
  simp only [mul_add, map_add] at h'
  rw [hN, hN, hN, hF2] at h'
  simp only [hsq] at h'
  rw [norm_add σ hσ3] at h'
  rw [hsq]
  linear_combination (-1 : E) * h'

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
