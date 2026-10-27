module

public import CFSG.Quasithin.Recognition.M12AscE3
public import CFSG.Quasithin.Recognition.M12AscD3

public section

namespace CFSG.Quasithin

open Subgroup Equiv

variable {G : Type*} [Group G] {z : G}

namespace OuterData

variable {m : AscModel z} {c : AscCox m} {y : G}

theorem Q8
    [Finite G] (h : OuterData c y) :
    ∃ l₀ ∈ h.L, l₀ ∉ h.K ∧ ∃ H : Subgroup G,
      (∀ g, g ∈ H ↔ g ∈ h.K ∧ l₀⁻¹ * g * l₀ ∈ h.K) ∧ Nonempty (↥H ≃* QuaternionGroup 2) := by
  classical
  refine ⟨c.ρ pa, (h.rho_mem_L pa).2 sign_pa, ?_, ?_⟩
  · intro hK
    have := ((h.rho_mem_K pa).1 hK).2
    rw [pa_not_norm] at this
    exact absurd this (by decide)
  let H : Subgroup G := h.K ⊓ h.K.comap (MulAut.conj (c.ρ pa)⁻¹).toMonoidHom
  have hH : ∀ g, g ∈ H ↔ g ∈ h.K ∧ (c.ρ pa)⁻¹ * g * c.ρ pa ∈ h.K := by
    intro g
    simp [H, Subgroup.mem_inf, Subgroup.mem_comap]
  refine ⟨H, hH, ?_⟩
  have hmemD : ∀ τ : Perm (Fin 6), c.ρ τ ∈ H ↔ Equiv.Perm.sign τ = 1 ∧ NormDb τ = true ∧
      NormDb (pa⁻¹ * τ * pa) = true := by
    intro τ
    rw [hH, h.rho_mem_K τ, conj_rho_rho (c := c) pa τ, h.rho_mem_K (pa⁻¹ * τ * pa), sign_conj_pa]
    constructor
    · rintro ⟨⟨h1, h2⟩, -, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h1, h3⟩
  have hmemE : ∀ τ : Perm (Fin 6), c.ρ τ * y ∈ H ↔ Equiv.Perm.sign τ = 1 ∧ NormEb τ = true ∧
      NormEb (pa⁻¹ * τ * (TA 2 * TA 4)) = true := by
    intro τ
    rw [hH, h.rhoy_mem_K τ, h.conj_rho_rhoy pa τ, outerAlpha_pa, h.rhoy_mem_K (pa⁻¹ * τ * (TA 2 * TA 4))]
    have : Equiv.Perm.sign (pa⁻¹ * τ * (TA 2 * TA 4)) = Equiv.Perm.sign τ := by
      rw [← outerAlpha_pa]
      simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, sign_pa, sign_outerAlpha]
    rw [this]
    constructor
    · rintro ⟨⟨h1, h2⟩, -, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h1, h3⟩
  have hcard : Nat.card H = 8 := by
    let f : ({τ : Perm (Fin 6) // Equiv.Perm.sign τ = 1 ∧ NormDb τ = true ∧
          NormDb (pa⁻¹ * τ * pa) = true} ⊕
        {τ : Perm (Fin 6) // Equiv.Perm.sign τ = 1 ∧ NormEb τ = true ∧
          NormEb (pa⁻¹ * τ * (TA 2 * TA 4)) = true}) → ↥H :=
      Sum.elim (fun τ => ⟨c.ρ τ.1, (hmemD τ.1).2 τ.2⟩) (fun τ => ⟨c.ρ τ.1 * y, (hmemE τ.1).2 τ.2⟩)
    have hf : Function.Bijective f := by
      constructor
      · rintro (⟨σ, hσ⟩ | ⟨σ, hσ⟩) (⟨τ, hτ⟩ | ⟨τ, hτ⟩) e
        · have := c.ρ_inj (congrArg Subtype.val e)
          subst this
          rfl
        · exact absurd (congrArg Subtype.val e) (h.rho_ne_rhoy σ τ)
        · exact absurd (congrArg Subtype.val e).symm (h.rho_ne_rhoy τ σ)
        · have := c.ρ_inj (mul_right_cancel (congrArg Subtype.val e))
          subst this
          rfl
      · rintro ⟨g, hg⟩
        have hgK : g ∈ h.K := ((hH g).1 hg).1
        obtain ⟨hgL, -⟩ := hgK
        obtain ⟨σ, hσ, rfl | rfl⟩ := hgL
        · exact ⟨Sum.inl ⟨σ, (hmemD σ).1 hg⟩, rfl⟩
        · exact ⟨Sum.inr ⟨σ, (hmemE σ).1 hg⟩, rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sum, card_H_D, card_H_E]
  have hi_mem : c.ρ taui ∈ H := (hmemD taui).2 taui_facts
  have hj_mem : c.ρ tauj * y ∈ H := (hmemE tauj).2 tauj_facts
  let i : ↥H := ⟨c.ρ taui, hi_mem⟩
  let j : ↥H := ⟨c.ρ tauj * y, hj_mem⟩
  have hαi : outerAlpha taui = evalWord TA wi := outerAlpha_word wi
  have hαj : outerAlpha tauj = evalWord TA wj := outerAlpha_word wj
  have hi_ord : orderOf i = 4 := by
    change orderOf i = 2 ^ 2
    apply orderOf_eq_prime_pow (p := 2) (n := 1)
    · intro hpow
      have : c.ρ (taui ^ 2) = 1 := by
        have := congrArg Subtype.val hpow
        simpa [i, map_pow] using this
      rw [← map_one c.ρ] at this
      exact taui_pow.1 (c.ρ_inj this)
    · have : c.ρ (taui ^ 4) = 1 := by rw [taui_pow.2, map_one]
      apply Subtype.ext
      simpa [i, map_pow] using this
  have hjj : j * j = i * i := by
    apply Subtype.ext
    show (c.ρ tauj * y) * (c.ρ tauj * y) = c.ρ taui * c.ρ taui
    calc (c.ρ tauj * y) * (c.ρ tauj * y) = c.ρ tauj * (y * c.ρ tauj) * y := by group
      _ = c.ρ tauj * (c.ρ (outerAlpha tauj) * y) * y := by rw [h.y_rho]
      _ = c.ρ tauj * c.ρ (outerAlpha tauj) * (y * y) := by group
      _ = c.ρ (tauj * evalWord TA wj * pa) := by rw [h.y_sq, ← c.ρ_pa, hαj, map_mul, map_mul]
      _ = c.ρ (taui * taui) := by rw [rel_jj]
      _ = c.ρ taui * c.ρ taui := by rw [map_mul]
  have hji : j * i * j⁻¹ = i⁻¹ := by
    have h1 : j * i = i⁻¹ * j := by
      apply Subtype.ext
      show (c.ρ tauj * y) * c.ρ taui = (c.ρ taui)⁻¹ * (c.ρ tauj * y)
      calc (c.ρ tauj * y) * c.ρ taui = c.ρ tauj * (y * c.ρ taui) := by group
        _ = c.ρ tauj * (c.ρ (outerAlpha taui) * y) := by rw [h.y_rho]
        _ = c.ρ (tauj * evalWord TA wi) * y := by rw [hαi, map_mul]; group
        _ = c.ρ (taui⁻¹ * tauj) * y := by rw [rel_ji]
        _ = (c.ρ taui)⁻¹ * (c.ρ tauj * y) := by rw [map_mul, map_inv]; group
    calc j * i * j⁻¹ = i⁻¹ * j * j⁻¹ := by rw [h1]
      _ = i⁻¹ := by group
  have hj_not : j ∉ zpowers i := by
    intro hj
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hj
    have hk' : c.ρ (taui ^ k) = c.ρ tauj * y := by
      have := congrArg Subtype.val hk
      simpa [i, map_zpow] using this
    exact h.rho_ne_rhoy (taui ^ k) tauj hk'
  exact exists_mulEquiv_quaternion i j hcard hi_ord hji hjj hj_not

end OuterData

end CFSG.Quasithin
