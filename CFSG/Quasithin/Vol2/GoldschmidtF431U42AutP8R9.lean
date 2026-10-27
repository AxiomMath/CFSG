module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R6
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R7

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem Thl_sq_ne_f : ∀ l ∈ Thl, comp l l ≠ fhatL := by decide +kernel

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Rho

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

theorem exists_rho (h : F55Ctx c R) : ∃ ρ ∈ C1G c R, ρ * ρ = c.iso.toG fhB := by
  set F := c.iso.toG fhB with hF
  obtain ⟨e⟩ := h.hD
  have hFR : F ∈ R := F_mem_R c h
  have hFc : ∀ r ∈ R, r * F = F * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.1 (h.hR.1 hr)
  have hF2 : F * F = 1 := F_sq c.iso
  have hcen : ∀ q : DihedralGroup 4 × DihedralGroup 4, e ⟨F, hFR⟩ * q = q * e ⟨F, hFR⟩ := by
    intro q
    obtain ⟨r, rfl⟩ := e.surjective q
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hFc r.1 r.2).symm)
  have h1 : e ⟨F, hFR⟩ ≠ 1 := by
    intro h1
    apply F_ne_one c.iso
    have := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have h2 : e ⟨F, hFR⟩ * e ⟨F, hFR⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    exact congrArg e (Subtype.ext hF2)
  obtain ⟨r, hr⟩ := Delta_central_sq _ h1 h2 hcen
  set ρ₀ : ↥R := e.symm r with hρ₀
  have hρ₀2 : (ρ₀ : G) * ρ₀ = F := by
    have : ρ₀ * ρ₀ = ⟨F, hFR⟩ := by
      apply e.injective
      rw [map_mul, hρ₀, MulEquiv.apply_symm_apply, hr]
    exact congrArg Subtype.val this
  obtain ⟨-, hdec⟩ := decomp_R c h
  obtain ⟨x, hx, u, hu, hxu⟩ := hdec ρ₀ ρ₀.2
  have hcom := C1G_comm_UG c h hx hu
  have hFC : F ∈ C1G c R := F_mem_C1G c h
  have hu2 : u * u = 1 := by
    have h3 : F = (x * x) * (u * u) := by
      calc F = (ρ₀ : G) * ρ₀ := hρ₀2.symm
        _ = (x * u) * (x * u) := by rw [← hxu]
        _ = x * (u * x) * u := by group
        _ = x * (x * u) * u := by rw [← hcom]
        _ = (x * x) * (u * u) := by group
    have h4 : u * u = (x * x)⁻¹ * F := by
      rw [h3]
      group
    have h5 : u * u ∈ C1G c R := by
      rw [h4]
      exact (C1G c R).mul_mem ((C1G c R).inv_mem ((C1G c R).mul_mem hx hx)) hFC
    exact C1G_inf_UG c ((UG c).mul_mem hu hu) h5
  refine ⟨x, hx, ?_⟩
  calc x * x = x * x * (u * u) := by rw [hu2]; group
    _ = (ρ₀ : G) * ρ₀ := by
      calc x * x * (u * u) = x * (x * u) * u := by group
        _ = x * (u * x) * u := by rw [hcom]
        _ = (x * u) * (x * u) := by group
        _ = (ρ₀ : G) * ρ₀ := by rw [← hxu]
    _ = F := hρ₀2

end Rho

end CFSG.Quasithin.H13.F431.U42Aut
