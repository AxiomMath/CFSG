module

public import CFSG.Walter.Ree.Thompson2.Alg.Unique

public section

namespace CFSG.Walter.Ree.T2.Alg

variable {k : Type} [Field k]

@[expose] noncomputable def c211 (σ : k ≃+* k) (a : ℕ) (z y u : k) : k :=
  psi3 σ a u * (σ z * z ^ 2) - psi3 σ a (-u) * (σ y * y ^ 2) - s2F σ a (-u) * (σ y * y) -
    σ (s1F a (-u) * y) - s1F a (-u) * y + (s1F a (-u) * y) ^ 2 + 1

variable {a : ℕ} {σ : k ≃+* k} {d : k} {S : k → k × k × k}

theorem coef211_eq (ha : Even a) (z y u : k) :
    coef211 σ a z y u = σ y * y ^ 2 * phi3 a (-u) - σ z * z ^ 2 * phi3 a u + 1 := by
  have he : Even (2 + a) := even_two.add ha
  rw [coef211, phi3, phi3, s1F, s1F, show -u - 1 = -(u + 1) by ring, he.neg_pow, he.neg_pow,
    neg_sq]
  ring

variable [CharP k 3]

theorem eq211_of (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (h1 : FE1C a S)
    (h2 : FE2C σ d S) (h3 : GF3C d S) (hT : T81C3 σ d S) :
    ∀ z y u : k, (z, y, u) ∈ hopkinsE σ → z * y * u ≠ 0 →
      u ^ (2 + a) - (u ^ 2 - 1) ^ (2 + a) ≠ 0 → coef211 σ a z y u * d = c211 σ a z y u := by
  intro z y u hE hzyu hD
  have hz : z ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hzyu)
  have hy : y ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hzyu)
  have hD' : (-u) ^ (2 + a) - ((-u) ^ 2 - 1) ^ (2 + a) ≠ 0 := by
    rwa [(even_two.add ha).neg_pow, neg_sq]
  have e := hT z y u hz hy hE
  rw [s3_eq ha haσ h1 h2 h3 hD, s3_eq ha haσ h1 h2 h3 hD', sFormula_thd, sFormula_thd,
    s2_eq ha haσ h1 h2 h3, fst_eq_s1F ha haσ h1 h2 h3] at e
  rw [coef211_eq ha, c211]
  linear_combination -e

end CFSG.Walter.Ree.T2.Alg
