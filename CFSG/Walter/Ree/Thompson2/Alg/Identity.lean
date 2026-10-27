module

public import CFSG.Walter.Ree.Thompson2.Alg.Unique

public section

namespace CFSG.Walter.Ree.T2.Alg

variable {k : Type} [Field k]
variable {a : ℕ} {σ : k ≃+* k} {d : k} {S : k → k × k × k}

theorem ESigma_fst_ne_zero (hσ2 : ∀ x : k, σ x * x ^ 2 = 1 → x = 1) {p : k × k × k}
    (hp : p ∈ ESigma k σ) : p.1 ≠ 0 := by
  obtain ⟨z, y, u⟩ := p
  obtain ⟨hE1, hE2, hu3⟩ := hp
  rintro (rfl : z = 0)
  have hy1 : y = 1 := hσ2 y (by
    simp only [map_zero, zero_mul, zero_sub] at hE1; linear_combination -hE1)
  subst hy1
  simp only [map_zero, mul_zero, map_one, mul_one, zero_sub] at hE2
  rw [← hE2] at hu3
  exact hu3 (by ring)

theorem ESigma_snd_ne_zero (hσ2 : ∀ x : k, σ x * x ^ 2 = 1 → x = 1) {p : k × k × k}
    (hp : p ∈ ESigma k σ) : p.2.1 ≠ 0 := by
  obtain ⟨z, y, u⟩ := p
  obtain ⟨hE1, hE2, hu3⟩ := hp
  rintro (rfl : y = 0)
  have hz1 : -z = 1 := hσ2 (-z) (by
    simp only [map_zero, zero_mul, sub_zero] at hE1
    rw [map_neg, neg_sq]; linear_combination -hE1)
  rw [show z = -1 by linear_combination -hz1] at hE2
  simp only [map_neg, map_one, map_zero, mul_zero, sub_zero] at hE2
  rw [← hE2] at hu3
  exact hu3 (by ring)

variable [CharP k 3]

theorem thompsonT_eq_zero_of_mem (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2)
    (hs1 : ∀ x : k, (S x).1 = ((x - 1) ^ a - x ^ a) / (x ^ a - (x ^ 2 - 1) ^ a))
    (hT : T81C1 σ S) {z y u : k} (hz : z ≠ 0) (hy : y ≠ 0) (hE : (z, y, u) ∈ hopkinsE σ) :
    thompsonT a z y u = 0 := by
  have h := hT z y u hz hy hE
  have hp := hs1 u
  have hm := hs1 (-u)
  rw [eq_div_iff (D1_ne_zero ha haσ u)] at hp
  rw [eq_div_iff (D1_ne_zero ha haσ (-u))] at hm
  rw [ha.neg_pow, neg_sq, show -u - 1 = -(u + 1) by ring, ha.neg_pow] at hm
  unfold thompsonT
  linear_combination (-z) * hp + y * hm + (u ^ a - (u ^ 2 - 1) ^ a) * h

theorem thompsonT_eq_zero (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2)
    (hσ2 : ∀ x : k, σ x * x ^ 2 = 1 → x = 1)
    (hs1 : ∀ x : k, (S x).1 = ((x - 1) ^ a - x ^ a) / (x ^ a - (x ^ 2 - 1) ^ a))
    (hT : T81C1 σ S) : ∀ p ∈ ESigma k σ, thompsonT a p.1 p.2.1 p.2.2 = 0 := fun _ hp =>
  thompsonT_eq_zero_of_mem ha haσ hs1 hT (ESigma_fst_ne_zero hσ2 hp)
    (ESigma_snd_ne_zero hσ2 hp) ⟨hp.1, hp.2.1⟩

theorem thompsonT_eq_zero_of (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2)
    (hσ2 : ∀ x : k, σ x * x ^ 2 = 1 → x = 1) (h1 : FE1C a S) (h2 : FE2C σ d S)
    (h3 : GF3C d S) (hT : T81C1 σ S) : ∀ p ∈ ESigma k σ, thompsonT a p.1 p.2.1 p.2.2 = 0 :=
  thompsonT_eq_zero ha haσ hσ2 (s1_eq ha haσ h1 h2 h3) hT

end CFSG.Walter.Ree.T2.Alg
