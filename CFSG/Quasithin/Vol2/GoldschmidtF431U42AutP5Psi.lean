module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutIface

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G} {z : G}

theorem conj_mem_centralizer {F c0 : G} (hc0 : c0 * F * c0⁻¹ = z) {y : G} (hy : y * F = F * y) :
    c0 * y * c0⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← hc0]
  calc c0 * y * c0⁻¹ * (c0 * F * c0⁻¹) = c0 * (y * F) * c0⁻¹ := by group
    _ = c0 * (F * y) * c0⁻¹ := by rw [hy]
    _ = c0 * F * c0⁻¹ * (c0 * y * c0⁻¹) := by group

@[expose] def psi (iso : AutIso M₁ M₂) (hcz : Subgroup.centralizer ({z} : Set G) ≤ M₁) {F : G}
    (c0 : G) (hc0 : c0 * F * c0⁻¹ = z) : ↥(Subgroup.centralizer ({F} : Set G)) →* ↥P1h where
  toFun y := iso.phi1.symm ⟨c0 * (y : G) * c0⁻¹,
    hcz (conj_mem_centralizer hc0 (Subgroup.mem_centralizer_singleton_iff.1 y.2))⟩
  map_one' := by
    apply iso.phi1.injective
    apply Subtype.ext
    simp
  map_mul' := by
    intro y₁ y₂
    apply iso.phi1.injective
    apply Subtype.ext
    simp only [MulEquiv.apply_symm_apply, map_mul, Subgroup.coe_mul]
    group

theorem phi1_psi (iso : AutIso M₁ M₂) (hcz : Subgroup.centralizer ({z} : Set G) ≤ M₁) {F : G}
    (c0 : G) (hc0 : c0 * F * c0⁻¹ = z) (y : ↥(Subgroup.centralizer ({F} : Set G))) :
    (iso.phi1 (psi iso hcz c0 hc0 y) : G) = c0 * (y : G) * c0⁻¹ := by
  simp only [psi, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.apply_symm_apply]

theorem psi_injective (iso : AutIso M₁ M₂) (hcz : Subgroup.centralizer ({z} : Set G) ≤ M₁)
    {F : G} (c0 : G) (hc0 : c0 * F * c0⁻¹ = z) : Function.Injective (psi iso hcz c0 hc0) := by
  intro y₁ y₂ h
  have h1 := congrArg (fun t => (iso.phi1 t : G)) h
  simp only [phi1_psi] at h1
  apply Subtype.ext
  exact mul_left_cancel (mul_right_cancel h1)

end CFSG.Quasithin.H13.F431.U42Aut
