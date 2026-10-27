module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcWord
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcParity
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

@[expose] def rho (r ξ : H) (s : ℕ) : H := ξ * r ^ s

theorem xi_zpow {x y : H} (hξ : ξ * ξ = 1) (hx : ξ * x * ξ = y) (n : ℤ) :
    ξ * x ^ n * ξ = y ^ n := by
  have hi : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right hξ
  have := map_zpow (MulAut.conj ξ) x n
  simpa [MulAut.conj_apply, hi, hx] using this

section Case7

variable (h : IsTutteSys s r l ξ Hs) (h7 : ξ * r * ξ = r⁻¹ ∧ ξ * l * ξ = l⁻¹)

include h h7

theorem rho_sq7 : rho r ξ s * rho r ξ s = 1 := by
  have e := xi_zpow h.xi_sq h7.1 (s : ℤ)
  simp only [zpow_natCast, inv_pow] at e
  calc rho r ξ s * rho r ξ s = (ξ * r ^ s * ξ) * r ^ s := by simp [rho, mul_assoc]
    _ = 1 := by rw [e]; simp

theorem rho_tx7 (a : ℤ) :
    rho r ξ s * tx r l a * rho r ξ s = (tx r l s)⁻¹ * tx r l ((s : ℤ) - a) := by
  have e1 := xi_zpow h.xi_sq h7.1 (s : ℤ)
  have e2 := xi_tx_7 h h7 a
  have e3 : ξ * (r ^ s * tx r l a) * ξ = r ^ (-(s : ℤ)) * tx r l (-a) := by
    calc ξ * (r ^ s * tx r l a) * ξ = (ξ * r ^ s * ξ) * (ξ * tx r l a * ξ) := by
          have := h.xi_sq
          calc ξ * (r ^ s * tx r l a) * ξ = ξ * r ^ s * (ξ * ξ) * tx r l a * ξ := by
                rw [this]; simp [mul_assoc]
            _ = _ := by simp [mul_assoc]
      _ = _ := by rw [← zpow_natCast, e1, e2, inv_zpow']
  have e4 := tx_shift r l 0 (-a) (s : ℤ)
  rw [tx_zero, inv_one, one_mul, zero_add] at e4
  calc rho r ξ s * tx r l a * rho r ξ s = ξ * (r ^ s * tx r l a) * ξ * r ^ s := by
        simp [rho, mul_assoc]
    _ = r ^ (-(s : ℤ)) * tx r l (-a) * r ^ s := by rw [e3]
    _ = _ := by rw [← zpow_natCast, e4]; congr 2; ring

theorem rho_tx7_s : rho r ξ s * tx r l s * rho r ξ s = (tx r l s)⁻¹ := by
  have e := rho_tx7 h h7 (s : ℤ)
  rwa [sub_self, tx_zero, mul_one] at e

theorem xs_hinv_xs7 :
    tx r l s * (rho r ξ s * tx r l s)⁻¹ * tx r l s = rho r ξ s * tx r l s := by
  have hρ : (rho r ξ s)⁻¹ = rho r ξ s := inv_eq_of_mul_eq_one_right (rho_sq7 h h7)
  rw [mul_inv_rev, hρ]
  simp

theorem parity_h7 : ∃ L : List ℤ, L.Pairwise (· > ·) ∧ (∀ t ∈ L, 1 ≤ t ∧ t < (s : ℤ)) ∧
    Odd L.length ∧ nfw r l (-1) L = rho r ξ s * tx r l s := by
  obtain ⟨ε, hε1, hε2⟩ := exists_parity h
  have hs1 : s - 1 < s := by have := h.one_le; omega
  have hmem : rho r ξ s * tx r l s ∈ Hs (s - 1) := h.rel
  obtain ⟨L, hL, hL1, hLeq⟩ := nf_exists h hs1 (-1) (Or.inr rfl) hmem
  have hL2 : ∀ t ∈ L, 1 ≤ t ∧ t < (s : ℤ) := fun t ht =>
    ⟨(hL1 t ht).1, by have := (hL1 t ht).2; have := h.one_le; omega⟩
  refine ⟨L, hL, hL2, ?_, hLeq⟩
  obtain ⟨hm, hεL⟩ := parity_nfw h ε hε1 (-1) (Or.inr rfl) hL2
  have hz : ε ⟨(rho r ξ s * tx r l s)⁻¹, inv_mem hmem⟩ = Multiplicative.ofAdd 1 := by
    refine ((hε2 _).1).2 ?_
    show tx r l s * (rho r ξ s * tx r l s)⁻¹ * tx r l s ∈ Hs (s - 1)
    rw [xs_hinv_xs7 h h7]
    exact hmem
  have hz' : ε ⟨rho r ξ s * tx r l s, hmem⟩ = Multiplicative.ofAdd 1 := by
    have : (⟨rho r ξ s * tx r l s, hmem⟩ : Hs (s - 1)) =
        (⟨(rho r ξ s * tx r l s)⁻¹, inv_mem hmem⟩ : Hs (s - 1))⁻¹ := by
      ext
      simp
    rw [this, map_inv, hz]
    decide
  have h3 : ε ⟨nfw r l (-1) L, hm⟩ = ε ⟨rho r ξ s * tx r l s, hmem⟩ := by
    congr 1
    exact Subtype.ext hLeq
  rw [h3, hz'] at hεL
  exact ZMod.natCast_eq_one_iff_odd.mp (Multiplicative.ofAdd.injective hεL.symm)

end Case7

end CFSG.Quasithin.Fan86.Tutte
