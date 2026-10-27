module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCoreRho

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem eq_ofAdd_one_of_ne_one (a : Multiplicative (ZMod 2)) (ha : a ≠ 1) :
    a = Multiplicative.ofAdd 1 := by
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h2 (Multiplicative.toAdd a) with h0 | h1
  · exact absurd (by simpa using congrArg Multiplicative.ofAdd h0) ha
  · simpa using congrArg Multiplicative.ofAdd h1

section Case8

variable (h : IsTutteSys s r l ξ Hs) (h8 : ξ * r * ξ = l⁻¹ ∧ ξ * l * ξ = r⁻¹)

include h h8

theorem rho_sq8 : rho r ξ s * rho r ξ s = tx r l s := by
  have e := xi_zpow h.xi_sq h8.1 (s : ℤ)
  rw [inv_zpow'] at e
  calc rho r ξ s * rho r ξ s = (ξ * r ^ (s : ℤ) * ξ) * r ^ (s : ℤ) := by
        simp [rho, mul_assoc]
    _ = tx r l s := by rw [e]; rfl

theorem rho_tx8 (a : ℤ) :
    rho r ξ s * tx r l a * (rho r ξ s)⁻¹ = tx r l s * (tx r l ((s : ℤ) - a))⁻¹ := by
  have hinv : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right h.xi_sq
  have e0 : rho r ξ s * tx r l a * (rho r ξ s)⁻¹ =
      ξ * (r ^ (s : ℤ) * tx r l a * r ^ (-(s : ℤ))) * ξ := by
    simp only [rho, mul_inv_rev, hinv, zpow_natCast, zpow_neg, mul_assoc]
  have hr := xi_zpow h.xi_sq h8.1
  rw [e0, xi_mul_conj h.xi_sq, xi_mul_conj h.xi_sq, hr, hr, xi_tx_8 h h8]
  unfold tx
  group

theorem xs_hinv_xs8 :
    tx r l s * (rho r ξ s * tx r l s)⁻¹ * tx r l s = rho r ξ s := by
  rw [mul_inv_rev, ← rho_sq8 h h8]
  group

theorem parity_h8 : ∃ L : List ℤ, L.Pairwise (· > ·) ∧ (∀ t ∈ L, 1 ≤ t ∧ t < (s : ℤ)) ∧
    Even L.length ∧ nfw r l 1 L = rho r ξ s * tx r l s := by
  obtain ⟨ε, hε1, hε2⟩ := exists_parity h
  have hs1 : s - 1 < s := by have := h.one_le; omega
  have hmem : rho r ξ s * tx r l s ∈ Hs (s - 1) := h.rel
  obtain ⟨L, hL, hL1, hLeq⟩ := nf_exists h hs1 1 (Or.inl rfl) hmem
  have hL2 : ∀ t ∈ L, 1 ≤ t ∧ t < (s : ℤ) := fun t ht =>
    ⟨(hL1 t ht).1, by have := (hL1 t ht).2; have := h.one_le; omega⟩
  refine ⟨L, hL, hL2, ?_, hLeq⟩
  obtain ⟨hm, hεL⟩ := parity_nfw h ε hε1 1 (Or.inl rfl) hL2
  have hρ : rho r ξ s ∉ Hs (s - 1) := by
    intro hρ
    apply h.x_not_mem s h.one_le le_rfl
    have := (Hs (s - 1)).mul_mem ((Hs (s - 1)).inv_mem hρ) hmem
    simpa using this
  have hz : ε ⟨(rho r ξ s * tx r l s)⁻¹, inv_mem hmem⟩ = 1 := by
    by_contra hne
    have h1 : ε ⟨(rho r ξ s * tx r l s)⁻¹, inv_mem hmem⟩ = Multiplicative.ofAdd 1 := by
      exact eq_ofAdd_one_of_ne_one _ hne
    have := ((hε2 _).1).1 h1
    change tx r l s * (rho r ξ s * tx r l s)⁻¹ * tx r l s ∈ Hs (s - 1) at this
    rw [xs_hinv_xs8 h h8] at this
    exact hρ this
  have hz' : ε ⟨rho r ξ s * tx r l s, hmem⟩ = 1 := by
    have : (⟨rho r ξ s * tx r l s, hmem⟩ : Hs (s - 1)) =
        (⟨(rho r ξ s * tx r l s)⁻¹, inv_mem hmem⟩ : Hs (s - 1))⁻¹ := by
      ext
      simp
    rw [this, map_inv, hz]
    simp
  have h3 : ε ⟨nfw r l 1 L, hm⟩ = ε ⟨rho r ξ s * tx r l s, hmem⟩ := by
    congr 1
    exact Subtype.ext hLeq
  rw [h3, hz'] at hεL
  exact ZMod.natCast_eq_zero_iff_even.mp
    (Multiplicative.ofAdd.injective (by simpa using hεL.symm))

end Case8

end CFSG.Quasithin.Fan86.Tutte
