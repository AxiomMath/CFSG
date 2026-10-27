module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.H13.L32A511Qd

public section

namespace CFSG.Quasithin.H13.Q511

open CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

theorem rkIdx_le_of_card_le (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V} {k : ℕ}
    (h : Nat.card V ≤ 2 ^ k * Nat.card ↥U) : rkIdx U ≤ k := by
  have h1 := rk_add_rkIdx U
  rw [card_eq_two_pow_rk hV, card_eq_two_pow hV U, ← pow_add] at h
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  omega

theorem rk_map_le_of_card_le (hV : ∀ v : V, v ^ 2 = 1) {s : MulAut V} {k : ℕ}
    (h : Nat.card V ≤ 2 ^ k * Nat.card ↥(fixV (Subgroup.zpowers s))) :
    rk ((⊤ : Subgroup V).map (commHom s)) ≤ k := by
  have h1 := rk_map_add_rk_inf (⊤ : Subgroup V) s
  rw [top_inf_eq, rk_top] at h1
  have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers s))
  have h3 := rkIdx_le_of_card_le hV h
  omega

theorem s3_conj_inv : ∀ a b : Equiv.Perm (Fin 3), a ^ 2 = 1 → a ≠ 1 → b ^ 3 = 1 →
    a * b * a⁻¹ * b = 1 := by
  decide

theorem inv_of_sq_eq_one {M : Type*} [Group M] {x s q : M} (hx3 : x ^ 3 = 1)
    (hq : q = s * x * s⁻¹ * x) (hq2 : q ≠ 1 → q * q = 1) (hxq : q ≠ 1 → x * q * x⁻¹ = q) :
    s * x * s⁻¹ = x⁻¹ := by
  by_cases hq1 : q = 1
  · rw [hq] at hq1
    exact eq_inv_of_mul_eq_one_left hq1
  · exfalso
    apply hq1
    have h2 := hq2 hq1
    have hc : Commute q x⁻¹ := by
      have h1 : q * x = x * q := by
        calc q * x = (x * q * x⁻¹) * x := by rw [hxq hq1]
          _ = x * q := by group
      exact (Commute.inv_right h1)
    have e : s * x * s⁻¹ = q * x⁻¹ := by rw [hq]; group
    have h3 : (s * x * s⁻¹) ^ 3 = 1 := by rw [← pow_conj, hx3]; group
    rw [e, hc.mul_pow, inv_pow, hx3, inv_one, mul_one, pow_three, h2, mul_one] at h3
    exact h3

end CFSG.Quasithin.H13.Q511
