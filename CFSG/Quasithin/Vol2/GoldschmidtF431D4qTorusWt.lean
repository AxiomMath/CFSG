module

public import CFSG.LieType.Steinberg.CentralExt.TrialityLift

public section

namespace CFSG.Quasithin.H13.F431.D4q.F48

open CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.LieType.Steinberg.TwistedD4

theorem not_dvd_of_abs_lt {N z : ℤ} (hz : z ≠ 0) (h : |z| < N) : ¬ N ∣ z :=
  fun hd => hz (Int.eq_zero_of_abs_lt_dvd hd h)

section Arith

variable {q : ℤ} (hq : 4 ≤ q)
include hq

theorem exp_not_dvd_d01 : ¬ (q ^ 3 - 1) ∣ (-q ^ 2 + q - 3) := by
  refine not_dvd_of_abs_lt (by nlinarith) ?_
  rw [abs_of_neg (by nlinarith)]
  nlinarith

theorem exp_not_dvd_d13 : ¬ (q ^ 3 - 1) ∣ (-q ^ 2 - q - 1) := by
  refine not_dvd_of_abs_lt (by nlinarith) ?_
  rw [abs_of_neg (by nlinarith)]
  nlinarith

theorem exp_not_dvd_d12 : ¬ (q ^ 3 - 1) ∣ (-q ^ 3 + 2 * q ^ 2 - 1) := by
  intro h
  have h2 : (q ^ 3 - 1) ∣ (-q ^ 3 + 2 * q ^ 2 - 1) + (q ^ 3 - 1) := dvd_add h dvd_rfl
  have h3 : (-q ^ 3 + 2 * q ^ 2 - 1) + (q ^ 3 - 1) = 2 * q ^ 2 - 2 := by ring
  rw [h3] at h2
  exact not_dvd_of_abs_lt (by nlinarith) (by rw [abs_of_pos (by nlinarith)]; nlinarith) h2

theorem exp_not_dvd_d23 : ¬ (q ^ 3 - 1) ∣ (q ^ 2 + q + 1) :=
  not_dvd_of_abs_lt (by nlinarith) (by rw [abs_of_pos (by nlinarith)]; nlinarith)

theorem exp_not_dvd_d11 : ¬ (q ^ 3 - 1) ∣ (q ^ 2 + 3 * q - 1) :=
  not_dvd_of_abs_lt (by nlinarith) (by rw [abs_of_pos (by nlinarith)]; nlinarith)

theorem exp_not_dvd_d10 : ¬ (q ^ 3 - 1) ∣ (2 * q ^ 2 + 2 * q + 2) :=
  not_dvd_of_abs_lt (by nlinarith) (by rw [abs_of_pos (by nlinarith)]; nlinarith)

end Arith

section Units

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem order_gen {q : ℕ} (hK : Nat.card K = q ^ 3) {g : Kˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    orderOf g = q ^ 3 - 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]

theorem exists_fpf {σ : K →+* K} {q : ℕ} (hq : 4 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) :
    ∃ (s : fixedUnits σ) (t : Kˣ),
      chi σ s t d01 ≠ 1 ∧ chi σ s t d13 ≠ 1 ∧ chi σ s t d12 ≠ 1 ∧
      chi σ s t d23 ≠ 1 ∧ chi σ s t d11 ≠ 1 ∧ chi σ s t d10 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord := order_gen hK hg
  have hN : (orderOf g : ℤ) = (q : ℤ) ^ 3 - 1 := by
    have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    rw [hord]
    push_cast [this]
    ring
  have hqz : (4 : ℤ) ≤ q := by exact_mod_cast hq
  have key : ∀ z : ℤ, ¬ ((q : ℤ) ^ 3 - 1) ∣ z → g ^ z ≠ 1 := fun z hz h =>
    hz (hN ▸ (orderOf_dvd_iff_zpow_eq_one.2 h))
  have hσu : ∀ u : Kˣ, Units.map σ.toMonoidHom u = u ^ q := units_map_eq_pow hσq
  have hσz : ∀ (z : ℤ), Units.map σ.toMonoidHom (g ^ z) = g ^ (z * q) := fun z => by
    rw [map_zpow, hσu, ← zpow_natCast, ← zpow_mul, mul_comm]
  set s0 : Kˣ := g ^ ((q : ℤ) ^ 2 + q + 1) with hs0
  set t : Kˣ := g ^ ((q : ℤ) - 1) with ht
  have hgN : g ^ ((q : ℤ) ^ 3 - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rw [hN])
  have hsfix : s0 ∈ fixedUnits σ := by
    rw [mem_fixedUnits]
    have h1 : Units.map σ.toMonoidHom s0 = s0 := by
      rw [hs0, hσz]
      have : (((q : ℤ) ^ 2 + q + 1) * q) = ((q : ℤ) ^ 2 + q + 1) + ((q : ℤ) ^ 3 - 1) := by ring
      rw [this, zpow_add, hgN, mul_one]
    simpa using congrArg (fun u : Kˣ => (u : K)) h1
  have hnorm : normU σ t = 1 := by
    rw [normU_eq_pow hσq, ht, ← zpow_natCast, ← zpow_mul, ← hgN]
    congr 1
    push_cast
    ring
  have hσt : Units.map σ.toMonoidHom t = g ^ (((q : ℤ) - 1) * q) := by rw [ht, hσz]
  have hσσt : Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t) =
      g ^ (((q : ℤ) - 1) * q * q) := by rw [hσt, hσz]
  refine ⟨⟨s0, hsfix⟩, t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show chi σ s0 t d01 ≠ 1
    rw [chi_d01]
    have : s0⁻¹ * t ^ 2 = g ^ (-(q : ℤ) ^ 2 + q - 3) := by rw [hs0, ht]; group
    rw [this]
    exact key _ (exp_not_dvd_d01 hqz)
  · show chi σ s0 t d13 ≠ 1
    rw [chi_d13, hnorm]
    have : s0⁻¹ * 1 = g ^ (-(q : ℤ) ^ 2 - q - 1) := by rw [hs0]; group
    rw [this]
    exact key _ (exp_not_dvd_d13 hqz)
  · show chi σ s0 t d12 ≠ 1
    rw [chi_d12, hσσt, hσt]
    have : t * g ^ (((q : ℤ) - 1) * q) * (g ^ (((q : ℤ) - 1) * q * q))⁻¹ =
        g ^ (-(q : ℤ) ^ 3 + 2 * q ^ 2 - 1) := by rw [ht]; group
    rw [this]
    exact key _ (exp_not_dvd_d12 hqz)
  · show chi σ s0 t d23 ≠ 1
    rw [chi_d23]
    exact key _ (exp_not_dvd_d23 hqz)
  · show chi σ s0 t d11 ≠ 1
    rw [chi_d11, hσσt, hσt]
    have : s0 * t * (g ^ (((q : ℤ) - 1) * q))⁻¹ * (g ^ (((q : ℤ) - 1) * q * q))⁻¹ =
        g ^ ((q : ℤ) ^ 2 + 3 * q - 1) * g ^ (-((q : ℤ) ^ 3 - 1)) := by rw [hs0, ht]; group
    rw [this, zpow_neg, hgN, inv_one, mul_one]
    exact key _ (exp_not_dvd_d11 hqz)
  · show chi σ s0 t d10 ≠ 1
    rw [chi_d10, hnorm]
    have : s0 ^ 2 * (1 : Kˣ)⁻¹ = g ^ (2 * (q : ℤ) ^ 2 + 2 * q + 2) := by rw [hs0]; group
    rw [this]
    exact key _ (exp_not_dvd_d10 hqz)

end Units

end CFSG.Quasithin.H13.F431.D4q.F48
