module

public import CFSG.Walter.Ree.Hopkins.Lemma24
public import CFSG.Walter.Ree.T2Interface
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

namespace CFSG.Walter.Ree.Hopkins

open CFSG.Walter.Ree.T2

variable {k : Type} [Field k] [CharP k 3] [Fintype k] {σ : k ≃+* k}

@[expose] def lhs26 (σ : k ≃+* k) (a : ℕ) (z y u : k) : k :=
  σ y * y ^ 2 * ((u + 1) ^ (2 + a) - u ^ (2 + a)) -
    σ z * z ^ 2 * ((u - 1) ^ (2 + a) - u ^ (2 + a)) + (u ^ (2 + a) - (u ^ 2 - 1) ^ (2 + a))

omit [Fintype k] [CharP k 3] in
theorem coef211_eq (a : ℕ) (z y u : k) (hD : u ^ (2 + a) - (u ^ 2 - 1) ^ (2 + a) ≠ 0) :
    coef211 σ a z y u = lhs26 σ a z y u / (u ^ (2 + a) - (u ^ 2 - 1) ^ (2 + a)) := by
  rw [coef211, lhs26]
  field_simp

section Basic

variable {a s : ℕ} (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (hsσ : ∀ x : k, (σ x * x ^ 2) ^ s = x)

omit [Fintype k] [CharP k 3] in
theorem sigmaP_mul (x y : k) : σ (x * y) * (x * y) ^ 2 = σ x * x ^ 2 * (σ y * y ^ 2) := by
  rw [map_mul]; ring

omit [Fintype k] [CharP k 3] in
theorem sigmaQ_mul (x y : k) : σ (x * y) * (x * y) = σ x * x * (σ y * y) := by
  rw [map_mul]; ring

include hsσ in
omit [Fintype k] [CharP k 3] in
theorem sigmaP_injective {x y : k} (h : σ x * x ^ 2 = σ y * y ^ 2) : x = y := by
  rw [← hsσ x, h, hsσ]

include hsσ in
omit [CharP k 3] in
theorem sigmaP_pow_s (x : k) : σ (x ^ s) * (x ^ s) ^ 2 = x := by
  have hinj : Function.Injective fun x : k => σ x * x ^ 2 := fun x y h => sigmaP_injective hsσ h
  obtain ⟨y, rfl⟩ := (Finite.injective_iff_surjective.mp hinj) x
  simp only
  rw [hsσ]

include haσ in
omit [Fintype k] [CharP k 3] in
theorem eq_or_eq_neg_of_sigmaQ {x y : k} (h : σ x * x = σ y * y) : x = y ∨ x = -y := by
  have h2 : x ^ 2 = y ^ 2 := by rw [← haσ x, h, haσ]
  have : (x - y) * (x + y) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

end Basic

section Identities

omit [Fintype k]

theorem two_eq_neg_one : (2 : k) = -1 := by linear_combination three_eq_zero (k := k)

theorem two_ne_zero_k : (2 : k) ≠ 0 := by
  rw [two_eq_neg_one]; exact neg_ne_zero.mpr one_ne_zero

omit [CharP k 3] in
theorem not_GF3 {u : k} (hu : u ^ 3 ≠ u) : u ≠ 0 ∧ u - 1 ≠ 0 ∧ u + 1 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl; exact hu (by ring)
  · intro h1; exact hu (by rw [sub_eq_zero.mp h1]; ring)
  · intro h1; exact hu (by rw [eq_neg_of_add_eq_zero_left h1]; ring)

omit [CharP k 3] in
theorem GF3_of {u : k} (h : u = 0 ∨ u = 1 ∨ u = -1) : u ^ 3 = u := by
  rcases h with rfl | rfl | rfl <;> ring

omit [CharP k 3] in
theorem v1_add_one {u : k} (h1 : u - 1 ≠ 0) : -u / (u - 1) + 1 = -1 / (u - 1) := by
  field_simp; ring

theorem v1_sub_one {u : k} (h1 : u - 1 ≠ 0) : -u / (u - 1) - 1 = (u + 1) / (u - 1) := by
  field_simp; linear_combination (-u) * three_eq_zero (k := k)

theorem v1_sq_sub_one {u : k} (h1 : u - 1 ≠ 0) :
    (-u / (u - 1)) ^ 2 - 1 = -(u + 1) / (u - 1) ^ 2 := by
  field_simp; linear_combination u * three_eq_zero (k := k)

omit [CharP k 3] in
theorem v2_add_one {u : k} (h2 : u + 1 ≠ 0) : -u / (u + 1) + 1 = 1 / (u + 1) := by
  field_simp; ring

theorem v2_sub_one {u : k} (h2 : u + 1 ≠ 0) : -u / (u + 1) - 1 = (u - 1) / (u + 1) := by
  field_simp; linear_combination (-u) * three_eq_zero (k := k)

theorem v2_sq_sub_one {u : k} (h2 : u + 1 ≠ 0) :
    (-u / (u + 1)) ^ 2 - 1 = (u - 1) / (u + 1) ^ 2 := by
  field_simp; linear_combination (-u) * three_eq_zero (k := k)

omit [CharP k 3] in
theorem v3_add_one {u : k} (h1 : u - 1 ≠ 0) : 1 / (u - 1) + 1 = u / (u - 1) := by
  field_simp; ring

theorem v3_sub_one {u : k} (h1 : u - 1 ≠ 0) : 1 / (u - 1) - 1 = -(u + 1) / (u - 1) := by
  field_simp; linear_combination three_eq_zero (k := k)

theorem v3_sq_sub_one {u : k} (h1 : u - 1 ≠ 0) :
    (1 / (u - 1)) ^ 2 - 1 = -(u * (u + 1)) / (u - 1) ^ 2 := by
  field_simp; linear_combination u * three_eq_zero (k := k)

omit [CharP k 3] in
theorem v1_inv {u : k} (h0 : u ≠ 0) (h1 : u - 1 ≠ 0) : -u⁻¹ / (u⁻¹ - 1) = 1 / (u - 1) := by
  have h1' : 1 - u ≠ 0 := fun h => h1 (by linear_combination -h)
  have : u⁻¹ - 1 = (1 - u) / u := by field_simp
  rw [this]
  field_simp
  ring

omit [CharP k 3] in
theorem v2_inv {u : k} (h0 : u ≠ 0) (h2 : u + 1 ≠ 0) : -u⁻¹ / (u⁻¹ + 1) = -1 / (u + 1) := by
  have : u⁻¹ + 1 = (1 + u) / u := by field_simp
  rw [this]
  have h2' : 1 + u ≠ 0 := by rwa [add_comm]
  field_simp
  ring

end Identities

section Main

variable {m a s : ℕ} (hk : Fintype.card k = 3 ^ m) (hm : Odd m)
  (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2)
  (hs : Odd s) (hsσ : ∀ x : k, (σ x * x ^ 2) ^ s = x)

include hk hm in
omit [CharP k 3] in
theorem neg_one_not_square' : ¬IsSquare (-1 : k) := by
  rw [FiniteField.isSquare_neg_one_iff, not_not, hk]
  obtain ⟨m', rfl⟩ := hm
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num

omit [Fintype k] [CharP k 3] in
theorem sigmaQ_pow (x : k) (n : ℕ) : σ (x ^ n) * x ^ n = (σ x * x) ^ n := by
  rw [map_pow, mul_pow]

include haσ hsσ in
omit [CharP k 3] [Fintype k] in
theorem eq_pm_one_of_pow_r {x : k} (hx : x ^ (2 + a) = 1) : x = 1 ∨ x = -1 := by
  have e : (σ x * x) ^ (2 + a) = (σ x * x ^ 2) ^ 2 := by
    rw [pow_add, haσ]; ring
  rw [← sigmaQ_pow, hx, map_one, one_mul] at e
  have hP : σ x * x ^ 2 = 1 ∨ σ x * x ^ 2 = -1 := by
    rcases sq_eq_one_iff.mp e.symm with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hP with h | h
  · left; apply sigmaP_injective hsσ; rw [h]; simp
  · right; apply sigmaP_injective hsσ; rw [h]; simp

include haσ hsσ in
omit [CharP k 3] [Fintype k] in
theorem eq_pm_of_pow_r {x y : k} (hy : y ≠ 0) (h : x ^ (2 + a) = y ^ (2 + a)) :
    x = y ∨ x = -y := by
  have h1 : (x / y) ^ (2 + a) = 1 := by rw [div_pow, h, div_self (pow_ne_zero _ hy)]
  rcases eq_pm_one_of_pow_r haσ hsσ h1 with h2 | h2
  · left; field_simp at h2; exact h2
  · right; field_simp at h2; linear_combination h2

@[expose] def zOf (σ : k ≃+* k) (s : ℕ) (y : k) : k := (σ y * y ^ 2 - 1) ^ s

@[expose] def uOf (σ : k ≃+* k) (s : ℕ) (y : k) : k :=
  σ (zOf σ s y) * zOf σ s y - σ y * y

include hsσ in
omit [CharP k 3] in
theorem sigmaP_zOf (y : k) : σ (zOf σ s y) * zOf σ s y ^ 2 = σ y * y ^ 2 - 1 :=
  sigmaP_pow_s hsσ _

include hsσ in
omit [CharP k 3] in
theorem mem_E (y : k) : (zOf σ s y, y, uOf σ s y) ∈ hopkinsE σ := by
  refine ⟨?_, rfl⟩
  simp only
  rw [sigmaP_zOf hsσ]; ring

include hsσ in
omit [CharP k 3] in
theorem eq_of_mem_E {z y u : k} (h : (z, y, u) ∈ hopkinsE σ) : z = zOf σ s y ∧ u = uOf σ s y := by
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  have hz : z = zOf σ s y := by
    apply sigmaP_injective hsσ
    rw [sigmaP_zOf hsσ]; linear_combination h1
  refine ⟨hz, ?_⟩
  rw [← h2, uOf, ← hz]

@[expose] def gOf (a : ℕ) (u : k) : k :=
  ((u ^ 2 - 1) ^ (2 + a) - (u - 1) ^ (2 + a)) / ((u + 1) ^ (2 + a) - (u - 1) ^ (2 + a))

include haσ hsσ in
omit [Fintype k] in
theorem A_ne_zero {u : k} (hu : u ^ 3 ≠ u) : (u + 1) ^ (2 + a) - (u - 1) ^ (2 + a) ≠ 0 := by
  obtain ⟨h0, h1, h2⟩ := not_GF3 hu
  intro h
  rcases eq_pm_of_pow_r haσ hsσ h1 (sub_eq_zero.mp h) with h' | h'
  · have : (2 : k) = 0 := by linear_combination h'
    exact two_ne_zero_k this
  · have : 2 * u = 0 := by linear_combination h'
    exact h0 ((mul_eq_zero.mp this).resolve_left two_ne_zero_k)

include hk hm haσ hsσ in
theorem D_ne_zero {u : k} (hu : u ^ 3 ≠ u) : u ^ (2 + a) - (u ^ 2 - 1) ^ (2 + a) ≠ 0 := by
  obtain ⟨h0, h1, h2⟩ := not_GF3 hu
  have hne : ¬IsSquare (-1 : k) := neg_one_not_square' hk hm
  intro h
  have hd : u ^ 2 - 1 ≠ 0 := by
    rw [show u ^ 2 - 1 = (u - 1) * (u + 1) by ring]; exact mul_ne_zero h1 h2
  rcases eq_pm_of_pow_r haσ hsσ hd (sub_eq_zero.mp h) with h' | h'
  ·
    exact hne ⟨u + 1, by linear_combination h' - (u + 1) * three_eq_zero (k := k)⟩
  ·
    exact hne ⟨u - 1, by linear_combination -h' + (u - 1) * three_eq_zero (k := k)⟩

@[expose] def AllSat26 (σ : k ≃+* k) (a : ℕ) : Prop :=
  ∀ z y u : k, (z, y, u) ∈ hopkinsE σ → z * y * u ≠ 0 →
    u ^ (2 + a) - (u ^ 2 - 1) ^ (2 + a) ≠ 0 → lhs26 σ a z y u = 0

include hs in
omit [CharP k 3] [Fintype k] in
theorem zOf_zero : zOf σ s (0 : k) = -1 := by
  simp [zOf, hs.neg_pow]

include hs hsσ in
omit [CharP k 3] in
theorem ne_zero_of_uOf {y : k} (hu : uOf σ s y ^ 3 ≠ uOf σ s y) :
    zOf σ s y ≠ 0 ∧ y ≠ 0 ∧ uOf σ s y ≠ 0 := by
  refine ⟨?_, ?_, (not_GF3 hu).1⟩
  · intro hz
    have h1 := sigmaP_zOf hsσ y
    rw [hz] at h1
    simp only [map_zero, zero_mul] at h1
    have hy : y = 1 := sigmaP_injective hsσ (by rw [map_one]; linear_combination -h1)
    apply hu
    rw [uOf, hz, hy]; norm_num
  · rintro rfl
    apply hu
    rw [uOf, zOf_zero hs]; norm_num

include hk hm haσ hs hsσ in
theorem sigmaP_eq_gOf (H : AllSat26 σ a) {y : k} (hu : uOf σ s y ^ 3 ≠ uOf σ s y) :
    σ y * y ^ 2 = gOf a (uOf σ s y) := by
  obtain ⟨hz, hy, hu0⟩ := ne_zero_of_uOf hs hsσ hu
  have h := H _ _ _ (mem_E hsσ y) (mul_ne_zero (mul_ne_zero hz hy) hu0) (D_ne_zero hk hm haσ hsσ hu)
  rw [lhs26, sigmaP_zOf hsσ] at h
  rw [gOf, eq_div_iff (A_ne_zero haσ hsσ hu)]
  linear_combination h

omit [Fintype k] [CharP k 3] in
theorem sigmaP_neg (x : k) : σ (-x) * (-x) ^ 2 = -(σ x * x ^ 2) := by rw [map_neg]; ring

omit [Fintype k] [CharP k 3] in
theorem sigmaQ_neg (x : k) : σ (-x) * -x = σ x * x := by rw [map_neg]; ring

include ha in
omit [Fintype k] [CharP k 3] in
theorem pow_r_neg_one : (-1 : k) ^ (2 + a) = 1 := (by
  obtain ⟨c, hc⟩ := ha; exact ⟨c + 1, by omega⟩ : Even (2 + a)).neg_one_pow

include ha haσ hs hsσ in
theorem mem_GF3_of_uOf (H : AllSat26 σ a) {y : k} (hu : uOf σ s y ^ 3 = uOf σ s y) :
    y = 0 ∨ y = 1 ∨ y = -1 := by
  have h3 := three_eq_zero (k := k)
  have hm1 := pow_r_neg_one (k := k) ha
  have hP := sigmaP_zOf hsσ y
  have hr0 : (0 : k) ^ (2 + a) = 0 := zero_pow (by omega)
  have h2r : (2 : k) ^ (2 + a) = 1 := by rw [two_eq_neg_one, hm1]
  have hm2r : (-2 : k) ^ (2 + a) = 1 := by
    rw [show (-2 : k) = 1 by linear_combination -h3, one_pow]
  rcases eq_of_cube_eq_self hu with hu0 | hu1 | hu2
  ·
    right; right
    have hQ : σ (zOf σ s y) * zOf σ s y = σ y * y := by rw [uOf] at hu0; linear_combination hu0
    rcases eq_or_eq_neg_of_sigmaQ haσ hQ with hzy | hzy
    · exfalso; rw [hzy] at hP; exact one_ne_zero (by linear_combination hP)
    · rw [hzy, sigmaP_neg] at hP
      apply sigmaP_injective hsσ
      simp only [map_neg, map_one, even_two, Even.neg_pow, one_pow, mul_one]
      linear_combination hP + (σ y * y ^ 2) * h3
  ·
    left
    by_contra hy
    have hz : zOf σ s y ≠ 0 := by
      intro hz
      rw [hz] at hP
      simp only [map_zero, zero_mul] at hP
      have hy1 : y = 1 := sigmaP_injective hsσ (by rw [map_one]; linear_combination -hP)
      rw [uOf, hz, hy1] at hu1
      simp only [map_zero, mul_zero, map_one, mul_one, zero_sub] at hu1
      exact two_ne_zero_k (by linear_combination -hu1)
    have h := H _ _ _ (mem_E hsσ y) (by rw [hu1, mul_one]; exact mul_ne_zero hz hy)
      (by rw [hu1]; simp [hr0])
    rw [lhs26, hu1, hP] at h
    simp only [one_add_one_eq_two, h2r, sub_self, one_pow, hr0, zero_sub, sub_zero] at h
    apply hy
    apply sigmaP_injective hsσ
    simp only [map_zero, zero_mul]
    linear_combination h
  ·
    right; left
    by_contra hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [uOf, zOf_zero hs] at hu2
      simp only [map_neg, map_one, mul_neg, mul_one, neg_neg, map_zero, mul_zero, sub_zero] at hu2
      exact two_ne_zero_k (by linear_combination hu2)
    have hz : zOf σ s y ≠ 0 := by
      intro hz
      rw [hz] at hP
      simp only [map_zero, zero_mul] at hP
      exact hy (sigmaP_injective hsσ (by rw [map_one]; linear_combination -hP))
    have hzyu : zOf σ s y * y * uOf σ s y ≠ 0 := by
      rw [hu2]; exact mul_ne_zero (mul_ne_zero hz hy0) (neg_ne_zero.mpr one_ne_zero)
    have h := H _ _ _ (mem_E hsσ y) hzyu (by rw [hu2]; simp [hr0, hm1])
    rw [lhs26, hu2, hP] at h
    simp only [neg_add_cancel, hr0, zero_sub, even_two, Even.neg_pow, one_pow, sub_self,
      hm1, mul_zero, sub_zero, show (-1 : k) - 1 = -2 by ring, hm2r] at h
    apply hy
    apply sigmaP_injective hsσ
    rw [map_one]
    linear_combination -h

include hk hm ha haσ hs hsσ in
theorem uOf_gOf (H : AllSat26 σ a) {v : k} (hv : v ^ 3 ≠ v) : uOf σ s (gOf a v ^ s) = v := by
  set T : Set k := {x | x ^ 3 ≠ x}
  have hmaps : Set.MapsTo (uOf σ s) T T := by
    intro y hy hyu
    rcases mem_GF3_of_uOf ha haσ hs hsσ H hyu with h | h | h <;> exact hy (GF3_of (by tauto))
  have hinj : Set.InjOn (uOf σ s) T := by
    intro y hy y' hy' h
    apply sigmaP_injective hsσ
    rw [sigmaP_eq_gOf hk hm haσ hs hsσ H (hmaps hy), sigmaP_eq_gOf hk hm haσ hs hsσ H (hmaps hy'),
      h]
  have hbij := ((Set.toFinite T).injOn_iff_bijOn_of_mapsTo hmaps).mp hinj
  obtain ⟨y, hy, hyv⟩ := hbij.surjOn hv
  have hP := sigmaP_eq_gOf hk hm haσ hs hsσ H (hmaps hy)
  rw [hyv] at hP
  rw [← hP, hsσ, hyv]

include ha in
omit [Fintype k] [CharP k 3] in
theorem even_r : Even (2 + a) := by obtain ⟨c, hc⟩ := ha; exact ⟨c + 1, by omega⟩

include haσ hsσ in
omit [Fintype k] [CharP k 3] in
theorem pow_r_ne_one {x : k} (hx : x ≠ 1) (hx' : x ≠ -1) : x ^ (2 + a) ≠ 1 := fun h => by
  rcases eq_pm_one_of_pow_r haσ hsσ h with h | h <;> contradiction

omit [Fintype k] in
theorem abm_facts {u : k} (hu : u ^ 3 ≠ u) :
    u - 1 ≠ 1 ∧ u - 1 ≠ -1 ∧ u + 1 ≠ 1 ∧ u + 1 ≠ -1 ∧ u ≠ u + 1 ∧ u ≠ -(u + 1) := by
  have h3 := three_eq_zero (k := k)
  obtain ⟨h0, h1, h2⟩ := not_GF3 hu
  refine ⟨fun h => hu ?_, fun h => h0 (by linear_combination h), fun h => h0 (by
    linear_combination h), fun h => hu ?_, fun h => one_ne_zero (by linear_combination -h),
    fun h => hu ?_⟩
  · rw [show u = -1 by linear_combination h + h3]; ring
  · rw [show u = 1 by linear_combination h - h3]; ring
  · rw [show u = 1 by linear_combination -h + u * h3]; ring

include ha haσ hsσ in
omit [Fintype k] in
theorem gOf_v1 {u : k} (hu : u ^ 3 ≠ u) :
    gOf a (-u / (u - 1)) = (u + 1) ^ (2 + a) * (1 - (u - 1) ^ (2 + a)) /
      ((u - 1) ^ (2 + a) * (1 - (u + 1) ^ (2 + a))) := by
  obtain ⟨h0, h1, h2⟩ := not_GF3 hu
  obtain ⟨a1, a2, a3, a4, -, -⟩ := abm_facts hu
  have hr := even_r ha
  have hα : (u - 1) ^ (2 + a) ≠ 0 := pow_ne_zero _ h1
  have hβ : (u + 1) ^ (2 + a) ≠ 0 := pow_ne_zero _ h2
  have hβ1 : 1 - (u + 1) ^ (2 + a) ≠ 0 := sub_ne_zero.mpr (pow_r_ne_one haσ hsσ a3 a4).symm
  rw [gOf, v1_sq_sub_one h1, v1_sub_one h1, v1_add_one h1, div_pow, div_pow, div_pow,
    hr.neg_pow, hr.neg_one_pow, ← pow_mul, mul_comm 2, pow_mul]
  field_simp

include haσ hsσ in
omit [Fintype k] in
theorem gOf_v2 {u : k} (hu : u ^ 3 ≠ u) :
    gOf a (-u / (u + 1)) = (u - 1) ^ (2 + a) * (1 - (u + 1) ^ (2 + a)) /
      ((u + 1) ^ (2 + a) * (1 - (u - 1) ^ (2 + a))) := by
  obtain ⟨h0, h1, h2⟩ := not_GF3 hu
  obtain ⟨a1, a2, a3, a4, -, -⟩ := abm_facts hu
  have hα : (u - 1) ^ (2 + a) ≠ 0 := pow_ne_zero _ h1
  have hβ : (u + 1) ^ (2 + a) ≠ 0 := pow_ne_zero _ h2
  have hα1 : 1 - (u - 1) ^ (2 + a) ≠ 0 := sub_ne_zero.mpr (pow_r_ne_one haσ hsσ a1 a2).symm
  rw [gOf, v2_sq_sub_one h2, v2_sub_one h2, v2_add_one h2, div_pow, div_pow, div_pow, one_pow,
    ← pow_mul, mul_comm 2, pow_mul]
  field_simp

include ha haσ hsσ in
omit [Fintype k] in
theorem gOf_v3 {u : k} (hu : u ^ 3 ≠ u) :
    gOf a (1 / (u - 1)) = (u + 1) ^ (2 + a) * (u ^ (2 + a) - (u - 1) ^ (2 + a)) /
      ((u - 1) ^ (2 + a) * (u ^ (2 + a) - (u + 1) ^ (2 + a))) := by
  obtain ⟨h0, h1, h2⟩ := not_GF3 hu
  obtain ⟨-, -, -, -, a5, a6⟩ := abm_facts hu
  have hr := even_r ha
  have hα : (u - 1) ^ (2 + a) ≠ 0 := pow_ne_zero _ h1
  have hμβ : u ^ (2 + a) - (u + 1) ^ (2 + a) ≠ 0 := by
    intro h
    rcases eq_pm_of_pow_r haσ hsσ h2 (sub_eq_zero.mp h) with h' | h'
    · exact a5 h'
    · exact a6 h'
  rw [gOf, v3_sq_sub_one h1, v3_sub_one h1, v3_add_one h1, div_pow, div_pow, div_pow,
    hr.neg_pow, hr.neg_pow, mul_pow, ← pow_mul, mul_comm 2, pow_mul]
  field_simp

omit [Fintype k] in
theorem v1_not_GF3 {u : k} (hu : u ^ 3 ≠ u) : (-u / (u - 1)) ^ 3 ≠ -u / (u - 1) := by
  have h3 := three_eq_zero (k := k)
  obtain ⟨h0, h1, h2⟩ := not_GF3 hu
  intro h
  rcases eq_of_cube_eq_self h with h' | h' | h' <;> field_simp at h'
  · exact h0 (by linear_combination -h')
  · exact hu (by rw [show u = -1 by linear_combination h' + u * h3]; ring)
  · exact one_ne_zero (by linear_combination -h')

omit [Fintype k] in
theorem v2_not_GF3 {u : k} (hu : u ^ 3 ≠ u) : (-u / (u + 1)) ^ 3 ≠ -u / (u + 1) := by
  have h3 := three_eq_zero (k := k)
  obtain ⟨h0, h1, h2⟩ := not_GF3 hu
  intro h
  rcases eq_of_cube_eq_self h with h' | h' | h' <;> field_simp at h'
  · exact h0 (by linear_combination -h')
  · exact hu (by rw [show u = 1 by linear_combination h' + u * h3]; ring)
  · exact one_ne_zero (by linear_combination h')

omit [Fintype k] in
theorem v3_not_GF3 {u : k} (hu : u ^ 3 ≠ u) : (1 / (u - 1)) ^ 3 ≠ 1 / (u - 1) := by
  have h3 := three_eq_zero (k := k)
  obtain ⟨h0, h1, h2⟩ := not_GF3 hu
  intro h
  rcases eq_of_cube_eq_self h with h' | h' | h' <;> field_simp at h'
  · exact one_ne_zero (by linear_combination h')
  · exact hu (by rw [show u = -1 by linear_combination -h' + h3]; ring)
  · exact h0 (by linear_combination h')

omit [Fintype k] [CharP k 3] in
theorem sigmaQ_inv (x : k) : σ x⁻¹ * x⁻¹ = (σ x * x)⁻¹ := by rw [map_inv₀, mul_inv]

include hk hm ha haσ hs hsσ in
theorem step6 (H : AllSat26 σ a) {u : k} (hu : u ^ 3 ≠ u) :
    σ (gOf a (-u / (u - 1)) ^ s) * gOf a (-u / (u - 1)) ^ s =
      (1 - -u / (u - 1)) / (1 - -u / (u + 1)) := by
  obtain ⟨h0, h1, h2⟩ := not_GF3 hu
  obtain ⟨a1, a2, a3, a4, -, -⟩ := abm_facts hu
  have hv₁ := v1_not_GF3 hu
  have hv₂ := v2_not_GF3 hu
  have hα : (u - 1) ^ (2 + a) ≠ 0 := pow_ne_zero _ h1
  have hβ : (u + 1) ^ (2 + a) ≠ 0 := pow_ne_zero _ h2
  have hα1 : 1 - (u - 1) ^ (2 + a) ≠ 0 := sub_ne_zero.mpr (pow_r_ne_one haσ hsσ a1 a2).symm
  have hβ1 : 1 - (u + 1) ^ (2 + a) ≠ 0 := sub_ne_zero.mpr (pow_r_ne_one haσ hsσ a3 a4).symm
  have hg := gOf_v1 ha haσ hsσ hu
  have hg0 : gOf a (-u / (u - 1)) ≠ 0 := by
    rw [hg]; exact div_ne_zero (mul_ne_zero hβ hα1) (mul_ne_zero hα hβ1)
  have hg2 : gOf a (-u / (u + 1)) = (gOf a (-u / (u - 1)))⁻¹ := by
    rw [gOf_v2 haσ hsσ hu, hg, inv_div]
  set g := gOf a (-u / (u - 1)) with hgdef
  set w := g ^ s with hwdef
  have hw0 : w ≠ 0 := pow_ne_zero _ hg0
  have hPw : σ w * w ^ 2 = g := sigmaP_pow_s hsσ g
  have e1 := uOf_gOf hk hm ha haσ hs hsσ H hv₁
  have e2 := uOf_gOf hk hm ha haσ hs hsσ H hv₂
  rw [hg2, inv_pow, ← hwdef] at e2
  rw [← hgdef, ← hwdef] at e1
  have hz : zOf σ s w⁻¹ = -zOf σ s w / w := by
    have e : σ w⁻¹ * w⁻¹ ^ 2 = g⁻¹ := by rw [map_inv₀, inv_pow, ← mul_inv, hPw]
    rw [zOf, zOf, e, hPw, show g⁻¹ - 1 = -(g - 1) / g by field_simp; ring, div_pow,
      hs.neg_pow, ← hwdef, neg_div]
  have hQw : σ w * w ≠ 0 := mul_ne_zero ((map_ne_zero σ).mpr hw0) hw0
  have hQz : σ (zOf σ s w⁻¹) * zOf σ s w⁻¹ = σ (zOf σ s w) * zOf σ s w / (σ w * w) := by
    rw [hz, neg_div, sigmaQ_neg, div_eq_mul_inv, sigmaQ_mul, sigmaQ_inv, ← div_eq_mul_inv]
  rw [uOf, hQz, sigmaQ_inv] at e2
  rw [uOf] at e1
  have h1v2 : 1 - -u / (u + 1) ≠ 0 := by
    intro h; apply hv₂; rw [show -u / (u + 1) = 1 by linear_combination -h]; ring
  generalize -u / (u - 1) = v₁ at e1 ⊢
  generalize -u / (u + 1) = v₂ at e2 h1v2 ⊢
  generalize σ (zOf σ s w) * zOf σ s w = X at e1 e2
  generalize σ w * w = W at e1 e2 hQw ⊢
  rw [eq_div_iff h1v2]
  field_simp at e2
  linear_combination e2 - e1

omit [Fintype k] [CharP k 3] in
theorem inv_not_GF3 {u : k} (hu : u ^ 3 ≠ u) : u⁻¹ ^ 3 ≠ u⁻¹ := by
  obtain ⟨h0, -, -⟩ := not_GF3 hu
  intro h
  apply hu
  have := congrArg (·⁻¹) h
  simp only [inv_pow, inv_inv] at this
  exact this

omit [Fintype k] in
theorem rhs6_eq {u : k} (hu : u ^ 3 ≠ u) :
    (1 - -u / (u - 1)) / (1 - -u / (u + 1)) = (1 - 1 / (u - 1)) / (1 - -1 / (u + 1)) := by
  have h3 := three_eq_zero (k := k)
  obtain ⟨h0, h1, h2⟩ := not_GF3 hu
  obtain ⟨a1, a2, a3, a4, -, -⟩ := abm_facts hu
  have e1 : 1 - -u / (u + 1) ≠ 0 := by
    intro h; apply v2_not_GF3 hu; rw [show -u / (u + 1) = 1 by linear_combination -h]; ring
  have e2 : 1 - -1 / (u + 1) ≠ 0 := by
    rw [show 1 - -1 / (u + 1) = (u - 1) / (u + 1) by field_simp; linear_combination h3]
    exact div_ne_zero h1 h2
  rw [div_eq_div_iff e1 e2]
  field_simp
  linear_combination (2 * u) * h3

include hk hm ha haσ hs hsσ in
theorem hopF_eq_zero_of_not_GF3 (H : AllSat26 σ a) {u : k} (hu : u ^ 3 ≠ u) :
    hopF (2 + a) u = 0 := by
  have h3 := three_eq_zero (k := k)
  obtain ⟨h0, h1, h2⟩ := not_GF3 hu
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := abm_facts hu
  have h6 := step6 hk hm ha haσ hs hsσ H hu
  have h6' := step6 hk hm ha haσ hs hsσ H (inv_not_GF3 hu)
  rw [v1_inv h0 h1, v2_inv h0 h2] at h6'
  rw [rhs6_eq hu, ← h6'] at h6
  rcases eq_or_eq_neg_of_sigmaQ haσ h6 with h7 | h7
  ·
    exfalso
    have e1 := uOf_gOf hk hm ha haσ hs hsσ H (v1_not_GF3 hu)
    have e3 := uOf_gOf hk hm ha haσ hs hsσ H (v3_not_GF3 hu)
    rw [h7, e3] at e1
    field_simp at e1
    exact hu (by rw [show u = -1 by linear_combination e1]; ring)
  ·
    have h8 : gOf a (-u / (u - 1)) = -gOf a (1 / (u - 1)) := by
      have := congrArg (fun x => σ x * x ^ 2) h7
      simp only [sigmaP_pow_s hsσ, sigmaP_neg] at this
      exact this
    rw [gOf_v1 ha haσ hsσ hu, gOf_v3 ha haσ hsσ hu] at h8
    have hα : (u - 1) ^ (2 + a) ≠ 0 := pow_ne_zero _ h1
    have hβ : (u + 1) ^ (2 + a) ≠ 0 := pow_ne_zero _ h2
    have hα1 : 1 - (u - 1) ^ (2 + a) ≠ 0 := sub_ne_zero.mpr (pow_r_ne_one haσ hsσ a1 a2).symm
    have hβ1 : 1 - (u + 1) ^ (2 + a) ≠ 0 := sub_ne_zero.mpr (pow_r_ne_one haσ hsσ a3 a4).symm
    have hμβ : u ^ (2 + a) - (u + 1) ^ (2 + a) ≠ 0 := by
      intro h
      rcases eq_pm_of_pow_r haσ hsσ h2 (sub_eq_zero.mp h) with h' | h'
      · exact a5 h'
      · exact a6 h'
    generalize hA : (u - 1) ^ (2 + a) = α at *
    generalize hB : (u + 1) ^ (2 + a) = β at *
    generalize hM : u ^ (2 + a) = μ at *
    have hE' : (1 - α) * (μ - β) + (μ - α) * (1 - β) = 0 := by
      field_simp at h8
      linear_combination h8
    rw [hopF, show u ^ 2 - u = u * (u - 1) by ring, show u ^ 2 + u = u * (u + 1) by ring,
      show u ^ 2 - 1 = (u - 1) * (u + 1) by ring, mul_pow, mul_pow, mul_pow, hA, hB, hM]
    linear_combination -hE' + (μ + α * β) * h3

include hk hm ha haσ hs hsσ in
theorem exists_triple (ha3 : a % 3 = 2) (haq : a + 3 < Fintype.card k) :
    ∃ z y u : k, (z, y, u) ∈ hopkinsE σ ∧ z * y * u ≠ 0 ∧
      u ^ (2 + a) - (u ^ 2 - 1) ^ (2 + a) ≠ 0 ∧ lhs26 σ a z y u ≠ 0 := by
  by_contra hcon
  have H : AllSat26 σ a := by
    intro z y u hE hzyu hD
    by_contra h
    exact hcon ⟨z, y, u, hE, hzyu, hD, h⟩
  have hF : ∀ u : k, hopF (2 + a) u = 0 := by
    intro u
    by_cases hu : u ^ 3 = u
    · exact hopF_GF3 (even_r ha) (by omega) hu
    · exact hopF_eq_zero_of_not_GF3 hk hm ha haσ hs hsσ H hu
  obtain ⟨u, hu⟩ := exists_hopF_ne_zero hk (even_r ha) (by omega) (by omega) (by omega)
  exact hu (hF u)

end Main

end CFSG.Walter.Ree.Hopkins
