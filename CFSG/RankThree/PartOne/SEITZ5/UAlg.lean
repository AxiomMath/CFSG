module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K}

theorem frob_inj {s t : K} (h : s ^ 2 = t ^ 2) : s = t := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (s + t) ^ 2 = 0 := by linear_combination h + (t ^ 2 + s * t) * h2
  have h0 : s + t = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linear_combination h0 - t * h2

theorem xi_pow_four (hσ : ∀ c, σ (σ c) = c) {ω a b : K} (hω : σ ω = ω ^ 2)
    (hω2 : ω ^ 2 + ω + 1 = 0) (ha : σ a = a) (hb : σ b = b)
    (hf : a ^ 4 + a ^ 2 * b ^ 2 + b ^ 4 + a ^ 2 + a * b + b ^ 2 = a ^ 2 * b + a * b ^ 2) :
    (a + ω * b) ^ 4 = a + ω * b := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set ξ : K := a + ω * b with hξ
  have hσξ : σ ξ = a + ω ^ 2 * b := by rw [hξ, map_add, map_mul, ha, hb, hω]
  have hN : (ξ ^ 2 + σ ξ) * σ (ξ ^ 2 + σ ξ) = 0 := by
    have e1 : σ (ξ ^ 2 + σ ξ) = (σ ξ) ^ 2 + ξ := by rw [map_add, map_pow, hσ]
    rw [e1, hσξ, hξ]
    linear_combination hf +
      (2 * a ^ 3 * b - 3 * a ^ 2 * b ^ 2 + 3 * a ^ 2 * b + 2 * a * b ^ 3 + 3 * a * b ^ 2 + a * b -
        b ^ 4 - 2 * b ^ 3 - b ^ 2 + ω ^ 4 * (b ^ 4 + b ^ 3) +
        ω ^ 3 * (2 * a * b ^ 3 - b ^ 4 - b ^ 3) + ω ^ 2 * (a ^ 2 * b ^ 2 + 3 * a * b ^ 2) +
        ω * (3 * a ^ 2 * b ^ 2 - 2 * a * b ^ 3 - 3 * a * b ^ 2 + b ^ 4 + 2 * b ^ 3 + b ^ 2)) *
        hω2 +
      (-a ^ 3 * b + a ^ 3 + a ^ 2 * b ^ 2 - a ^ 2 * b - a * b ^ 3 - a * b ^ 2 - a * b + b ^ 3) * h2
  have h0 : ξ ^ 2 + σ ξ = 0 := by
    rcases mul_eq_zero.1 hN with h | h
    · exact h
    · have : ξ ^ 2 + σ ξ = 0 := by
        have h' := congrArg σ h
        rwa [hσ, map_zero] at h'
      exact this
  have hσξ2 : σ ξ = ξ ^ 2 := by linear_combination h0 - ξ ^ 2 * h2
  calc ξ ^ 4 = (ξ ^ 2) ^ 2 := by ring
    _ = (σ ξ) ^ 2 := by rw [hσξ2]
    _ = σ (ξ ^ 2) := by rw [map_pow]
    _ = σ (σ ξ) := by rw [hσξ2]
    _ = ξ := hσ ξ

theorem eqn_of_relations {a x y γ sγ sy sxy : K} (hax : a ^ 2 = x) (hy : sy ^ 2 = y)
    (hxy : sxy ^ 2 = x + y) (hγ : sγ ^ 2 = γ) (hγdef : γ = x ^ 2 + x * y + y ^ 2)
    (h : γ + sγ = x * (y + sy) + y * (x + y + sxy) + y * (y + sy)) :
    a ^ 4 + a ^ 2 * sy ^ 2 + sy ^ 4 + a ^ 2 + a * sy + sy ^ 2 = a ^ 2 * sy + a * sy ^ 2 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  subst hax hy
  have hsxy : sxy = a + sy := by
    apply frob_inj
    linear_combination hxy - (a * sy) * h2
  have hsγ : sγ = a ^ 2 + a * sy + sy ^ 2 := by
    apply frob_inj
    rw [hγ, hγdef]
    linear_combination (-(a ^ 3 * sy + a * sy ^ 3 + a ^ 2 * sy ^ 2)) * h2
  subst hsxy hsγ hγdef
  linear_combination h + (a ^ 2 * sy ^ 2 + sy ^ 4 + sy ^ 3) * h2

end CFSG.RankThree.PartOne.SEITZ5
