module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3AutShape

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open DihedralGroup
open scoped commutatorElement

variable {R : Type*} [Group R]

theorem cent_transfer (φ : MulAut (DihedralGroup 4 × R)) (d₀ : DihedralGroup 4)
    (PV : DihedralGroup 4 → Prop) (hV : ∀ y, d₀ * y = y * d₀ ↔ PV y)
    (hd₀ : ¬ (d₀ = r 0 ∨ d₀ = r 2)) (hsq : d₀ * d₀ = 1) (hfix : φ (a0, 1) = (a0, 1)) :
    (∀ h : DihedralGroup 4 × R, PV h.1 ↔ inA (φ h).1) ∨
      (∀ h : DihedralGroup 4 × R, PV h.1 ↔ inB (φ h).1) := by
  rcases image_shape φ d₀ hd₀ with ⟨_, h1⟩ | ⟨hnc, hcent, _⟩
  · rw [hfix] at h1
    exact absurd h1 a0_ne_one
  · set g := φ (d₀, 1) with hg
    have hgg : g * g = 1 := by
      rw [hg, ← map_mul, ← map_one φ]
      congr 1
      exact Prod.ext (by simpa using hsq) (by simp)
    have hsq' : g.1 * g.1 = 1 := congrArg Prod.fst hgg
    have key : ∀ h : DihedralGroup 4 × R,
        (d₀ * h.1 = h.1 * d₀) ↔ (g.1 * (φ h).1 = (φ h).1 * g.1) := by
      intro h
      constructor
      · intro hh
        have e : ((d₀, 1) : DihedralGroup 4 × R) * h = h * (d₀, 1) := Prod.ext hh (by simp)
        have e' := congrArg φ e
        rw [map_mul, map_mul] at e'
        exact congrArg Prod.fst e'
      · intro hh
        have e : g * φ h = φ h * g := Prod.ext hh (hcent _)
        have e' : φ (((d₀, 1) : DihedralGroup 4 × R) * h) = φ (h * (d₀, 1)) := by
          rw [map_mul, map_mul]; exact e
        exact congrArg Prod.fst (φ.injective e')
    rcases cent_cases g.1 hsq' hnc with h | h
    · left; intro x; rw [← hV, key, h]
    · right; intro x; rw [← hV, key, h]

theorem combos (φ : MulAut (DihedralGroup 4 × R)) (hfix : φ (a0, 1) = (a0, 1)) :
    ((∀ h : DihedralGroup 4 × R, inA h.1 ↔ inA (φ h).1) ∧
        (∀ h : DihedralGroup 4 × R, inB h.1 ↔ inB (φ h).1)) ∨
      ((∀ h : DihedralGroup 4 × R, inA h.1 ↔ inB (φ h).1) ∧
        (∀ h : DihedralGroup 4 × R, inB h.1 ↔ inA (φ h).1)) := by
  have hA := cent_transfer φ (sr 0) inA (fun y => cent_A (sr 0) (by decide) (by decide) y)
    (by decide) (by decide) hfix
  have hB := cent_transfer φ (sr 1) inB (fun y => cent_B (sr 1) (by decide) (by decide) y)
    (by decide) (by decide) hfix
  have x0 : inA (sr 0 : DihedralGroup 4) := by decide
  have y0 : ¬ inB (sr 0 : DihedralGroup 4) := by decide
  have x1 : inB (sr 1 : DihedralGroup 4) := by decide
  have y1 : ¬ inA (sr 1 : DihedralGroup 4) := by decide
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exfalso
    have h1 := (hB ((sr 1 : DihedralGroup 4), (1 : R))).1 x1
    exact y1 ((hA ((sr 1 : DihedralGroup 4), (1 : R))).2 h1)
  · exact Or.inl ⟨hA, hB⟩
  · exact Or.inr ⟨hA, hB⟩
  · exfalso
    have h1 := (hA ((sr 0 : DihedralGroup 4), (1 : R))).1 x0
    exact y0 ((hB ((sr 0 : DihedralGroup 4), (1 : R))).2 h1)

theorem swap_absurd (φ : MulAut (DihedralGroup 4 × R)) (p : ℕ) (hodd : Odd p) (hφ : φ ^ p = 1)
    (hAB : ∀ h : DihedralGroup 4 × R, inA h.1 ↔ inB (φ h).1)
    (hBA : ∀ h : DihedralGroup 4 × R, inB h.1 ↔ inA (φ h).1) : False := by
  have key : ∀ n : ℕ, ∀ h : DihedralGroup 4 × R, inA h.1 ↔ inB ((φ ^ (2 * n + 1)) h).1 := by
    intro n
    induction n with
    | zero => intro h; simpa using hAB h
    | succ n ih =>
      intro h
      have e : φ ^ (2 * (n + 1) + 1) = φ ^ (2 * n + 1) * (φ * φ) := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring, pow_succ, pow_succ, mul_assoc]
      rw [e, MulAut.mul_apply, MulAut.mul_apply]
      exact ((hAB h).trans (hBA (φ h))).trans (ih (φ (φ h)))
  obtain ⟨k, hk⟩ := hodd
  have hall : ∀ h : DihedralGroup 4 × R, inA h.1 ↔ inB h.1 := by
    intro h
    have := key k h
    rw [← hk, hφ] at this
    simpa using this
  have x0 : inA (sr 0 : DihedralGroup 4) := by decide
  have y0 : ¬ inB (sr 0 : DihedralGroup 4) := by decide
  exact y0 ((hall ((sr 0 : DihedralGroup 4), (1 : R))).1 x0)

theorem fixed_case (φ : MulAut (DihedralGroup 4 × R)) (p : ℕ) (hodd : Odd p) (hφ : φ ^ p = 1)
    (hfix : φ (a0, 1) = (a0, 1)) (i : ℕ) :
    (∀ h : DihedralGroup 4 × R, inA h.1 ↔ inA ((φ ^ i) h).1) ∧
      (∀ h : DihedralGroup 4 × R, inB h.1 ↔ inB ((φ ^ i) h).1) := by
  rcases combos φ hfix with ⟨hA, hB⟩ | ⟨hAB, hBA⟩
  · induction i with
    | zero => exact ⟨fun h => by simp, fun h => by simp⟩
    | succ i ih =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [pow_succ, MulAut.mul_apply]
        exact (hA h).trans (ih.1 (φ h))
      · rw [pow_succ, MulAut.mul_apply]
        exact (hB h).trans (ih.2 (φ h))
  · exact (swap_absurd φ p hodd hφ hAB hBA).elim

end CFSG.Quasithin.Fan86.Sigma3
