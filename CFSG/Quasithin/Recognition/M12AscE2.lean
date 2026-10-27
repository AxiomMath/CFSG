module

public import CFSG.Quasithin.Recognition.M12AscL3
public import Certificates.Certificate17009


public section

namespace CFSG.Quasithin

open Subgroup Equiv

variable {G : Type*} [Group G] {z : G}

theorem outerAlpha_pa : outerAlpha pa = TA 2 * TA 4 := by
  unfold pa
  rw [map_mul]
  exact congrArg₂ (· * ·) (outerAlpha_gen 2) (outerAlpha_gen 4)

theorem outerAlpha_sig3 : outerAlpha sig3 = TA 3 * TA 2 := by
  unfold sig3
  rw [map_mul]
  exact congrArg₂ (· * ·) (outerAlpha_gen 3) (outerAlpha_gen 2)

theorem sign_pa : Equiv.Perm.sign pa = 1 :=
  Certificates.certificate17009.1
theorem sign_sig3 : Equiv.Perm.sign sig3 = 1 :=
  Certificates.certificate17009.2.1

theorem pa_not_norm : NormDb pa = false :=
  Certificates.certificate17009.2.2.1
theorem sig3_not_norm : NormDb sig3 = false :=
  Certificates.certificate17009.2.2.2.1
theorem pa_sig3_not_norm : NormDb (pa⁻¹ * sig3) = false :=
  Certificates.certificate17009.2.2.2.2.1

theorem stab_D : ∀ τ : Perm (Fin 6), Equiv.Perm.sign τ = 1 → NormDb τ = true →
    NormDb (pa⁻¹ * τ * pa) = true → NormDb (sig3⁻¹ * τ * sig3) = true → τ = 1 :=
  Certificates.certificate17009.2.2.2.2.2.1

theorem stab_E : ∀ τ : Perm (Fin 6), Equiv.Perm.sign τ = 1 → NormEb τ = true →
    NormEb (pa⁻¹ * τ * (TA 2 * TA 4)) = true → NormEb (sig3⁻¹ * τ * (TA 3 * TA 2)) = true →
    False :=
  Certificates.certificate17009.2.2.2.2.2.2.1

theorem card_H_D : Nat.card {τ : Perm (Fin 6) // Equiv.Perm.sign τ = 1 ∧ NormDb τ = true ∧
    NormDb (pa⁻¹ * τ * pa) = true} = 4 :=
  Certificates.certificate17009.2.2.2.2.2.2.2.1

theorem card_H_E : Nat.card {τ : Perm (Fin 6) // Equiv.Perm.sign τ = 1 ∧ NormEb τ = true ∧
    NormEb (pa⁻¹ * τ * (TA 2 * TA 4)) = true} = 4 :=
  Certificates.certificate17009.2.2.2.2.2.2.2.2

namespace OuterData

variable {m : AscModel z} {c : AscCox m} {y : G}

theorem conj_rho_rhoy (h : OuterData c y) (σ τ : Perm (Fin 6)) :
    (c.ρ σ)⁻¹ * (c.ρ τ * y) * c.ρ σ = c.ρ (σ⁻¹ * τ * outerAlpha σ) * y := by
  calc (c.ρ σ)⁻¹ * (c.ρ τ * y) * c.ρ σ = (c.ρ σ)⁻¹ * c.ρ τ * (y * c.ρ σ) := by group
    _ = (c.ρ σ)⁻¹ * c.ρ τ * (c.ρ (outerAlpha σ) * y) := by rw [h.y_rho]
    _ = c.ρ (σ⁻¹ * τ * outerAlpha σ) * y := by rw [map_mul, map_mul, map_inv]; group

theorem conj_rho_rho (σ τ : Perm (Fin 6)) :
    (c.ρ σ)⁻¹ * c.ρ τ * c.ρ σ = c.ρ (σ⁻¹ * τ * σ) := by
  rw [map_mul, map_mul, map_inv]

theorem pts
    [Finite G] (h : OuterData c y) : Nat.card (↥h.L ⧸ h.K.subgroupOf h.L) = 10 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (h.K.subgroupOf h.L)
  have h2 : Nat.card (h.K.subgroupOf h.L) = Nat.card h.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.K_le_L).toEquiv
  rw [h2, h.L_card, h.K_card] at h1
  omega

theorem smul_mk_eq_iff
    (h : OuterData c y) (g ℓ : ↥h.L) :
    g • (QuotientGroup.mk ℓ : ↥h.L ⧸ h.K.subgroupOf h.L) = QuotientGroup.mk ℓ ↔
      (ℓ : G)⁻¹ * (g : G) * (ℓ : G) ∈ h.K := by
  rw [show g • (QuotientGroup.mk ℓ : ↥h.L ⧸ h.K.subgroupOf h.L) = QuotientGroup.mk (g * ℓ) from rfl,
    QuotientGroup.eq]
  constructor
  · intro hmem
    have : ((g * ℓ)⁻¹ * ℓ : ↥h.L) ∈ h.K.subgroupOf h.L := hmem
    have h2 := (Subgroup.mem_subgroupOf.1 this)
    have h3 : (ℓ : G)⁻¹ * (g : G) * (ℓ : G) = (((g * ℓ)⁻¹ * ℓ : ↥h.L) : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      group
    rw [h3]
    exact inv_mem h2
  · intro hmem
    have : ((g * ℓ)⁻¹ * ℓ : ↥h.L) = (ℓ⁻¹ * g * ℓ)⁻¹ := by group
    rw [this]
    refine inv_mem (Subgroup.mem_subgroupOf.2 ?_)
    simpa using hmem

end OuterData

end CFSG.Quasithin
