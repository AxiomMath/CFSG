module

public import CFSG.RankThree.PartOne.S11b.Sec11Algebra
import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartOne

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mul_zpow_mem_of_commutators_mem {T Q : Subgroup G}
    (hQn : ∀ q ∈ Q, ∀ t ∈ T, t * q * t⁻¹ ∈ Q)
    (hTT : ∀ s ∈ T, ∀ t ∈ T, s⁻¹ * t⁻¹ * s * t ∈ Q) {s t : G} (hs : s ∈ T) (ht : t ∈ T)
    (m : ℤ) : (s ^ m * t ^ m)⁻¹ * (s * t) ^ m ∈ Q := by
  set Q' : Subgroup T := Q.subgroupOf T with hQ'
  have hnorm : Q'.Normal := by
    refine ⟨fun q hq t => ?_⟩
    rw [hQ', Subgroup.mem_subgroupOf] at hq ⊢
    exact hQn q hq t t.2
  let φ : T →* T ⧸ Q' := QuotientGroup.mk' Q'
  set s' : T := ⟨s, hs⟩
  set t' : T := ⟨t, ht⟩
  have hcomm1 : φ ⁅s', t'⁆ = 1 := by
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    rw [hQ', Subgroup.mem_subgroupOf]
    have := hTT s⁻¹ (T.inv_mem hs) t⁻¹ (T.inv_mem ht)
    simpa [commutatorElement_def, s', t'] using this
  have hcomm : Commute (φ s') (φ t') := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact hcomm1
  have h := hcomm.mul_zpow m
  have h' : φ (s' ^ m * t' ^ m) = φ ((s' * t') ^ m) := by
    rw [map_mul, map_zpow, map_zpow, map_zpow, map_mul, h]
  have h2 : (s' ^ m * t' ^ m)⁻¹ * (s' * t') ^ m ∈ Q' := by
    rw [← QuotientGroup.eq]
    exact h'
  have := Subgroup.mem_subgroupOf.mp (hQ' ▸ h2)
  simpa [s', t'] using this

theorem zpow_zpow_pow_eq (g : G) (a b : ℤ) (n : ℕ) : ((g ^ a) ^ b) ^ n = (g ^ n) ^ (a * b) := by
  rw [← zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

theorem exists_coprime_relation {p : ℕ} (hp : p.Prime) (e₁ e₂ : ℤ) :
    ∃ k₁ k₂ : ℤ, e₁ * k₁ + e₂ * k₂ = 0 ∧ ¬ ((p : ℤ) ∣ k₁ ∧ (p : ℤ) ∣ k₂) := by
  by_cases h : e₁ = 0 ∧ e₂ = 0
  · refine ⟨1, 0, by simp [h.1, h.2], ?_⟩
    rintro ⟨h1, -⟩
    have := Int.eq_one_of_dvd_one (by positivity) h1
    exact hp.one_lt.ne' (by exact_mod_cast this)
  · have hpos : 0 < Int.gcd e₁ e₂ := by
      rcases not_and_or.mp h with h1 | h1
      · exact Int.gcd_pos_iff.mpr (Or.inl h1)
      · exact Int.gcd_pos_iff.mpr (Or.inr h1)
    obtain ⟨g, m', n', hg, hmn, he₁, he₂⟩ := Int.exists_gcd_one' hpos
    refine ⟨n', -m', ?_, ?_⟩
    · rw [he₁, he₂]
      ring
    · rintro ⟨h1, h2⟩
      have hb := Int.gcd_eq_gcd_ab m' n'
      rw [hmn] at hb
      have h3 : (p : ℤ) ∣ m' := by simpa using h2
      have h4 : (p : ℤ) ∣ 1 := by
        have h5 : (1 : ℤ) = m' * Int.gcdA m' n' + n' * Int.gcdB m' n' := by exact_mod_cast hb
        rw [h5]
        exact dvd_add (dvd_mul_of_dvd_left h3 _) (dvd_mul_of_dvd_left h1 _)
      have := Int.eq_one_of_dvd_one (by positivity) h4
      exact hp.one_lt.ne' (by exact_mod_cast this)

variable [Finite G]

theorem false_of_symmetric_types {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (T Q : Subgroup G) (ζ : G)
    (hQT : Q ≤ T) (hζQ : ζ ∈ Q) (hQc : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q)
    (hζz : ∀ t ∈ T, t * ζ = ζ * t) (hTT : ∀ s ∈ T, ∀ t ∈ T, s⁻¹ * t⁻¹ * s * t ∈ Q)
    (hQT' : ∀ q ∈ Q, ∀ t ∈ T, q⁻¹ * t⁻¹ * q * t ∈ zpowers ζ) (g₁ g₂ : G) (hg₁ : g₁ ∈ T)
    (hg₂ : g₂ ∈ T) (hind : ∀ k₁ k₂ : ℤ, g₁ ^ k₁ * g₂ ^ k₂ ∈ Q → (p : ℤ) ∣ k₁ ∧ (p : ℤ) ∣ k₂)
    (e₁ e₂ : ℤ) (hge₁ : g₁ ^ p = ζ ^ e₁) (hge₂ : g₂ ^ p = ζ ^ e₂) (hpζ : p ∣ orderOf ζ)
    (hexp : orderOf ζ = Monoid.exponent Q)
    (hfull : ∀ t ∈ T, t ∉ Q → ∃ m : ℤ, ¬ (p : ℤ) ∣ m ∧ ∃ z ∈ Q,
      orderOf (t ^ m * z) = p * Monoid.exponent Q) : False := by
  have hWQ : zpowers ζ ≤ Q := (zpowers_le).mpr hζQ
  have hQn : ∀ q ∈ Q, ∀ t ∈ T, t * q * t⁻¹ ∈ Q := by
    intro q hq t ht
    have h1 := hQT' q hq t⁻¹ (T.inv_mem ht)
    have h2 : q⁻¹ * (t⁻¹)⁻¹ * q * t⁻¹ ∈ Q := hWQ h1
    have h3 : q * (q⁻¹ * (t⁻¹)⁻¹ * q * t⁻¹) ∈ Q := Q.mul_mem hq h2
    simpa [mul_assoc] using h3
  obtain ⟨k₁, k₂, hk, hk'⟩ := exists_coprime_relation hp e₁ e₂
  set x' : G := g₁ ^ k₁ with hx'
  set y' : G := g₂ ^ k₂ with hy'
  have hx'T : x' ∈ T := T.zpow_mem hg₁ k₁
  have hy'T : y' ∈ T := T.zpow_mem hg₂ k₂
  have hxyQ : x' * y' ∉ Q := fun h => hk' (hind k₁ k₂ h)
  obtain ⟨m, hm, z, hz, hord⟩ := hfull (x' * y') (T.mul_mem hx'T hy'T) hxyQ
  have hx''T : x' ^ m ∈ T := T.zpow_mem hx'T m
  have hy''T : y' ^ m ∈ T := T.zpow_mem hy'T m
  have hxy : (x' ^ m) ^ p * (y' ^ m) ^ p = 1 := by
    rw [hx', hy', zpow_zpow_pow_eq, zpow_zpow_pow_eq, hge₁, hge₂, ← zpow_mul, ← zpow_mul,
      ← zpow_add]
    have : e₁ * (k₁ * m) + e₂ * (k₂ * m) = 0 := by
      calc e₁ * (k₁ * m) + e₂ * (k₂ * m) = (e₁ * k₁ + e₂ * k₂) * m := by ring
        _ = 0 := by rw [hk, zero_mul]
    rw [this, zpow_zero]
  have hq₁ : (x' ^ m * y' ^ m)⁻¹ * (x' * y') ^ m ∈ Q :=
    mul_zpow_mem_of_commutators_mem hQn hTT hx'T hy'T m
  have hWz : ∀ w ∈ zpowers ζ, ∀ t ∈ T, t * w = w * t := by
    intro w hw t ht
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact (Commute.zpow_right (show Commute t ζ from hζz t ht) k).eq
  have hz'' : ((x' ^ m * y' ^ m)⁻¹ * (x' * y') ^ m) * z ∈ Q := Q.mul_mem hq₁ hz
  have hord' : orderOf (x' ^ m * y' ^ m * (((x' ^ m * y' ^ m)⁻¹ * (x' * y') ^ m) * z)) =
      p * Monoid.exponent Q := by
    have : x' ^ m * y' ^ m * (((x' ^ m * y' ^ m)⁻¹ * (x' * y') ^ m) * z) = (x' * y') ^ m * z := by
      group
    rw [this]
    exact hord
  exact Sec11Algebra.false_of_subgroup_relations hp hp5 T Q (zpowers ζ) hQT hWQ (x' ^ m) (y' ^ m)
    _ hx''T hy''T hz'' hQc hWz (hTT _ hy''T _ hx''T) (fun q hq => hQT' q hq _ hx''T)
    (fun q hq => hQT' q hq _ hy''T) hxy (hexp ▸ hpζ) hord'

end CFSG.RankThree.PartOne
