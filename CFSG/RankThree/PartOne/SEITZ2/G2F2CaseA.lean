module

public import CFSG.RankThree.PartOne.SEITZ2.G2F2Seven
public import CFSG.RankThree.PartOne.SEITZ2.G2F2Conj

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6
open scoped commutatorElement Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem Wg_x7 (c : K) : Wg K * xp 7 c * (Wg K)⁻¹ = xp 3 c :=
  Wg_conj_xp (q := 7) (by norm_num) (by norm_num) rf_e1_7 reflect_7 c

theorem Wg_x4 (c : K) : Wg K * xp 4 c * (Wg K)⁻¹ = xp 8 c :=
  Wg_conj_xp (q := 8) (by norm_num) (by norm_num) reflect_4 reflect_e0_8 c

theorem comap_le_of_gens {H : Subgroup (adjointGroup .G2 K)} {k : Subfield K}
    (hRH : ∀ p < 12, ∀ c ∈ k, xp p c ∈ H) {c : ℕ → K} (hc1 : c 1 = 0) {μ : K}
    (hy : ordProd c * xp 10 μ * (ordProd c)⁻¹ ∈ H) :
    Gam (c 0) (c 4) μ ≤ H.comap (MulAut.conj (ordProd c * Wg K)).toMonoidHom := by
  have hconj : ∀ g : adjointGroup .G2 K, (ordProd c * Wg K) * g * (ordProd c * Wg K)⁻¹ =
      ordProd c * (Wg K * g * (Wg K)⁻¹) * (ordProd c)⁻¹ := fun g => by group
  have hcomm : ∀ d : K, ordProd c * xp 7 d * (ordProd c)⁻¹ = xp 7 d := fun d => by
    rw [(ordProd_commute_x7 c d).eq]
    group
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl | rfl)
  · show (ordProd c * Wg K) * xp 0 1 * (ordProd c * Wg K)⁻¹ ∈ H
    rw [hconj, Wg_xp0, hcomm]
    exact hRH 7 (by norm_num) 1 k.one_mem
  · show (ordProd c * Wg K) * xp 2 μ * (ordProd c * Wg K)⁻¹ ∈ H
    rw [hconj, Wg_xp2]
    exact hy
  · show (ordProd c * Wg K) * (xp 7 1 * xp 0 (c 0)) * (ordProd c * Wg K)⁻¹ ∈ H
    rw [conj_mul_eq, hconj, hconj, Wg_x7, Wg_xp0, hcomm, conj_x3, mul_assoc, ← xp_add]
    rw [mul_one, CharTwo.add_self_eq_zero, xp_zero, mul_one]
    exact hRH 3 (by norm_num) 1 k.one_mem
  · show (ordProd c * Wg K) * (xp 4 1 * xp 0 (c 4)) * (ordProd c * Wg K)⁻¹ ∈ H
    rw [conj_mul_eq, hconj, hconj, Wg_x4, Wg_xp0, hcomm, conj_x8, hc1]
    simp only [mul_zero, add_zero, mul_one, xp_zero, one_mul]
    rw [mul_assoc, ← xp_add, CharTwo.add_self_eq_zero, xp_zero, mul_one]
    exact hRH 8 (by norm_num) 1 k.one_mem

theorem x2_x3 (c d : K) : xp 2 c * xp 3 d * (xp 2 c)⁻¹ = xp 3 d := by
  have h := x2_conj_dv c 0 d
  simpa [dv, xp_zero] using h

theorem x2_x7 (c d : K) : xp 2 c * xp 7 d * (xp 2 c)⁻¹ = xp 7 d * xp 3 (c * d) := by
  have h := x2_conj_dv c d 0
  simpa [dv, xp_zero] using h

section Main

variable [Finite K]

theorem caseA_full_three {k : Subfield K} (hk : Nat.card k = 2) {d : ℕ} (hd : d.Prime)
    (hd2 : d ≠ 2) (hK : Nat.card K = Nat.card k ^ d) {H : Subgroup (adjointGroup .G2 K)}
    (hRH : ∀ p < 12, ∀ c ∈ k, xp p c ∈ H) {c : ℕ → K} (hc1 : c 1 = 0) {μ : K} (hμ : μ ≠ 0)
    (hy : ordProd c * xp 10 μ * (ordProd c)⁻¹ ∈ H) (hirr : ¬ (c 0 ∈ k ∧ c 4 ∈ k)) :
    Full H 3 := by
  have hle := comap_le_of_gens hRH hc1 hy
  have hL : ∀ a : K, xp 3 a * xp 7 (c 0 * a) ∈ H := by
    intro a
    have h' : (ordProd c * Wg K) * xp 7 a * (ordProd c * Wg K)⁻¹ ∈ H :=
      hle (gamma_full hk hd hd2 hK hμ hirr a)
    rwa [show (ordProd c * Wg K) * xp 7 a * (ordProd c * Wg K)⁻¹ =
      ordProd c * (Wg K * xp 7 a * (Wg K)⁻¹) * (ordProd c)⁻¹ by group, Wg_x7, conj_x3] at h'
  have h2 : xp 2 (1 : K) ∈ H := hRH 2 (by norm_num) 1 k.one_mem
  have hx3 : ∀ a : K, xp 3 (c 0 * a) ∈ H := by
    intro a
    have e1 := hL a
    have e2 := H.mul_mem (H.mul_mem h2 e1) (H.inv_mem h2)
    rw [conj_mul_eq, x2_x3, x2_x7, one_mul] at e2
    have e3 := H.mul_mem (H.inv_mem e1) e2
    rwa [show (xp 3 a * xp 7 (c 0 * a))⁻¹ * (xp 3 a * (xp 7 (c 0 * a) * xp 3 (c 0 * a))) =
      xp 3 (c 0 * a) by group] at e3
  intro t
  by_cases h0 : c 0 = 0
  · have := hL t
    rwa [h0, zero_mul, xp_zero, mul_one] at this
  · have := hx3 (t / c 0)
    rwa [show c 0 * (t / c 0) = t by field_simp] at this

end Main

end CFSG.RankThree.PartOne.SEITZ2
