module

public import CFSG.Quasithin.Recognition.M12AscE2

public section

namespace CFSG.Quasithin

open Subgroup Equiv

variable {G : Type*} [Group G] {z : G}

@[expose] def wi : List (Fin 5) := [0, 1, 0, 2, 1, 0, 3, 2, 1, 0, 4, 3, 2, 1]

@[expose] def wj : List (Fin 5) := [1, 0, 2, 1, 3, 2]

@[expose] def taui : Perm (Fin 6) := evalWord swapGen wi
@[expose] def tauj : Perm (Fin 6) := evalWord swapGen wj

theorem taui_facts : Equiv.Perm.sign taui = 1 ∧ NormDb taui = true ∧
    NormDb (pa⁻¹ * taui * pa) = true := by decide +kernel

theorem tauj_facts : Equiv.Perm.sign tauj = 1 ∧ NormEb tauj = true ∧
    NormEb (pa⁻¹ * tauj * (TA 2 * TA 4)) = true := by decide +kernel

theorem taui_pow : taui ^ 2 ≠ 1 ∧ taui ^ 4 = 1 := by decide +kernel

theorem rel_jj : tauj * evalWord TA wj * pa = taui * taui := by decide +kernel

theorem rel_ji : tauj * evalWord TA wi = taui⁻¹ * tauj := by decide +kernel

theorem sign_conj_pa (τ : Perm (Fin 6)) :
    Equiv.Perm.sign (pa⁻¹ * τ * pa) = Equiv.Perm.sign τ := by
  simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, sign_pa]

namespace OuterData

variable {m : AscModel z} {c : AscCox m} {y : G}

theorem L3
    [Finite G] (h : OuterData c y) :
    ∀ a b : Fin 3 → (↥h.L ⧸ h.K.subgroupOf h.L), Function.Injective a → Function.Injective b →
      ∃! g : ↥h.L, ∀ i, g • a i = b i := by
  classical
  let ℓ2 : ↥h.L := ⟨c.ρ pa, (h.rho_mem_L pa).2 sign_pa⟩
  let ℓ3 : ↥h.L := ⟨c.ρ sig3, (h.rho_mem_L sig3).2 sign_sig3⟩
  let p : Fin 3 → (↥h.L ⧸ h.K.subgroupOf h.L) :=
    ![QuotientGroup.mk 1, QuotientGroup.mk ℓ2, QuotientGroup.mk ℓ3]
  have hmk : ∀ a b : ↥h.L, (QuotientGroup.mk a : ↥h.L ⧸ h.K.subgroupOf h.L) = QuotientGroup.mk b ↔
      ((a⁻¹ * b : ↥h.L) : G) ∈ h.K := fun a b => QuotientGroup.eq
  have hne01 : (QuotientGroup.mk 1 : ↥h.L ⧸ h.K.subgroupOf h.L) ≠ QuotientGroup.mk ℓ2 := by
    rw [Ne, hmk]
    intro hK
    have : c.ρ pa ∈ h.K := by simpa [ℓ2] using hK
    have := ((h.rho_mem_K pa).1 this).2
    rw [pa_not_norm] at this
    exact absurd this (by decide)
  have hne02 : (QuotientGroup.mk 1 : ↥h.L ⧸ h.K.subgroupOf h.L) ≠ QuotientGroup.mk ℓ3 := by
    rw [Ne, hmk]
    intro hK
    have : c.ρ sig3 ∈ h.K := by simpa [ℓ3] using hK
    have := ((h.rho_mem_K sig3).1 this).2
    rw [sig3_not_norm] at this
    exact absurd this (by decide)
  have hne12 : (QuotientGroup.mk ℓ2 : ↥h.L ⧸ h.K.subgroupOf h.L) ≠ QuotientGroup.mk ℓ3 := by
    rw [Ne, hmk]
    intro hK
    have : c.ρ (pa⁻¹ * sig3) ∈ h.K := by
      have e : ((ℓ2⁻¹ * ℓ3 : ↥h.L) : G) = c.ρ (pa⁻¹ * sig3) := by
        simp [ℓ2, ℓ3, map_mul, map_inv]
      rw [← e]
      exact hK
    have := ((h.rho_mem_K _).1 this).2
    rw [pa_sig3_not_norm] at this
    exact absurd this (by decide)
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact absurd hij hne01
      | exact absurd hij.symm hne01
      | exact absurd hij hne02
      | exact absurd hij.symm hne02
      | exact absurd hij hne12
      | exact absurd hij.symm hne12
  have hfree : ∀ g : ↥h.L, (∀ i, g • p i = p i) → g = 1 := by
    intro g hg
    have h1 := (h.smul_mk_eq_iff g 1).1 (hg 0)
    have h2 := (h.smul_mk_eq_iff g ℓ2).1 (hg 1)
    have h3 := (h.smul_mk_eq_iff g ℓ3).1 (hg 2)
    obtain ⟨g0, hg0⟩ := g
    simp only [Subgroup.coe_one, inv_one, one_mul, mul_one] at h1
    obtain ⟨τ, hτ, rfl | rfl⟩ := hg0
    · have k1 := ((h.rho_mem_K τ).1 h1).2
      have k2 : NormDb (pa⁻¹ * τ * pa) = true := by
        have e : (c.ρ pa)⁻¹ * c.ρ τ * c.ρ pa = c.ρ (pa⁻¹ * τ * pa) := by
          rw [map_mul, map_mul, map_inv]
        have := h2
        simp only [ℓ2] at this
        rw [e] at this
        exact ((h.rho_mem_K _).1 this).2
      have k3 : NormDb (sig3⁻¹ * τ * sig3) = true := by
        have e : (c.ρ sig3)⁻¹ * c.ρ τ * c.ρ sig3 = c.ρ (sig3⁻¹ * τ * sig3) := by
          rw [map_mul, map_mul, map_inv]
        have := h3
        simp only [ℓ3] at this
        rw [e] at this
        exact ((h.rho_mem_K _).1 this).2
      have := stab_D τ hτ k1 k2 k3
      subst this
      apply Subtype.ext
      simp
    · exfalso
      have k1 := ((h.rhoy_mem_K τ).1 h1).2
      have k2 : NormEb (pa⁻¹ * τ * (TA 2 * TA 4)) = true := by
        have := h2
        simp only [ℓ2] at this
        rw [h.conj_rho_rhoy, outerAlpha_pa] at this
        exact ((h.rhoy_mem_K _).1 this).2
      have k3 : NormEb (sig3⁻¹ * τ * (TA 3 * TA 2)) = true := by
        have := h3
        simp only [ℓ3] at this
        rw [h.conj_rho_rhoy, outerAlpha_sig3] at this
        exact ((h.rhoy_mem_K _).1 this).2
      exact stab_E τ hτ k1 k2 k3
  exact sharp3_of_free h.L_card h.pts p hp hfree

end OuterData

end CFSG.Quasithin
