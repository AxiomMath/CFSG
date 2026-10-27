module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.FixedData
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg.Assembly

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame

theorem commute_pow_three_of_commutator_mem {G : Type*} [Group G] {a b ζ : G}
    (h : IsHeisPair a b ζ) {g : G} (hg : ⁅g, a⁆ ∈ Subgroup.zpowers ζ) : Commute (g ^ 3) a := by
  set z := ⁅g, a⁆ with hz
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨s, hs⟩ := h.exists_ζ_pow hg
    rw [hs, ← pow_mul, mul_comm, pow_mul, h.ζ_pow, one_pow]
  have hga : g * a * g⁻¹ = z * a := by rw [hz, commutatorElement_def]; group
  have hpow : ∀ k : ℕ, g ^ k * a * (g ^ k)⁻¹ = z ^ k * a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc g ^ (k + 1) * a * (g ^ (k + 1))⁻¹ = g * (g ^ k * a * (g ^ k)⁻¹) * g⁻¹ := by
            rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
        _ = g * (z ^ k * a) * g⁻¹ := by rw [ih]
        _ = z ^ k * (g * a * g⁻¹) := by
            rw [← mul_assoc, ((h.commute_of_mem_zpowers hg g).symm.pow_right k).eq]
            simp only [mul_assoc]
        _ = z ^ (k + 1) * a := by rw [hga, pow_succ, mul_assoc]
  have h3 := hpow 3
  rw [hz3, one_mul] at h3
  exact mul_inv_eq_iff_eq_mul.mp h3

theorem orderOf_dvd_of_commute_of_mem_P {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    {C P : Subgroup (PSU3 2 p)} (hF : FixedData C P) {u x : PSU3 2 p}
    (hu : u ∈ P) (hu1 : u ≠ 1) (hux : x * u = u * x) :
    orderOf x ∣ 3 * (2 ^ p + 1) := by
  obtain ⟨a, b, ζ, hH, hker, -, -, hPeq, hpow⟩ :=
    exists_pair_of_card_nine_pow hp h5 P hF.card_P
  have ha : projSU3 hp.one_le a ∈ P := by
    rw [hPeq, ← hH.E_eq_closure]
    exact Subgroup.mem_map_of_mem _ hH.a_mem_E
  have ha1 : projSU3 hp.one_le a ≠ 1 := fun h1 => hH.a_not_mem_zpowers ((hker a).mp h1)
  obtain ⟨c, -, hc⟩ := hF.trans u hu hu1 _ ha ha1
  have hx : Commute (c * x * c⁻¹) (projSU3 hp.one_le a) := by
    rw [← hc]
    show c * x * c⁻¹ * (c * u * c⁻¹) = c * u * c⁻¹ * (c * x * c⁻¹)
    calc c * x * c⁻¹ * (c * u * c⁻¹) = c * (x * u) * c⁻¹ := by group
      _ = c * (u * x) * c⁻¹ := by rw [hux]
      _ = c * u * c⁻¹ * (c * x * c⁻¹) := by group
  obtain ⟨g, hg⟩ := projSU3_surjective hp.one_le (c * x * c⁻¹)
  have hga : ⁅g, a⁆ ∈ Subgroup.zpowers ζ :=
    IsHeisPair.commutator_mem_of_commute (projSU3 hp.one_le) (fun g hg => (hker g).mp hg)
      (by rw [hg]; exact hx)
  have h3 : (g ^ 3) ^ (2 ^ p + 1) = 1 := hpow _ (commute_pow_three_of_commutator_mem hH hga)
  have hord : orderOf (c * x * c⁻¹) ∣ 3 * (2 ^ p + 1) := by
    rw [← hg]
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, pow_mul, h3, map_one]
  have hconj : orderOf (c * x * c⁻¹) = orderOf x := by
    have := (MulAut.conj c).orderOf_eq x
    rwa [MulAut.conj_apply] at this
  rwa [hconj] at hord

theorem not_commute_of_orderOf_prime_dvd {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    {C P : Subgroup (PSU3 2 p)} (hF : FixedData C P) (hr : r.Prime) (hrd : r ∣ 2 ^ p - 1)
    {u x : PSU3 2 p} (hu : u ∈ P) (hu1 : u ≠ 1) (hx : orderOf x = r) : ¬ (x * u = u * x) := by
  intro hux
  have h1 := orderOf_dvd_of_commute_of_mem_P hp h5 hF hu hu1 hux
  rw [hx] at h1
  have hmod := two_pow_mod_three_of_odd (hp.odd_of_ne_two (by omega))
  have hpos : 0 < 2 ^ p := by positivity
  rcases (Nat.Prime.dvd_mul hr).mp h1 with h3 | h2
  · have : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3
    subst this
    omega
  · have h2' : r ∣ (2 ^ p + 1) - (2 ^ p - 1) := Nat.dvd_sub h2 hrd
    have h22 : (2 ^ p + 1) - (2 ^ p - 1) = 2 := by omega
    rw [h22] at h2'
    have hr2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2'
    subst hr2
    have : 2 ∣ 2 ^ p := dvd_pow_self 2 (by omega)
    omega

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame
