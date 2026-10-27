module

public import CFSG.Quasithin.H13.AS91Sec5Todd
public import CFSG.Quasithin.H13.AS91Sec5TwoCRed

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.Quasithin.H

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

structure ToddCore where
  φ : ↥c.G1 →* Equiv.Perm (Fin 24)
  φ_mem : ∀ h, φ h ∈ AutPerm
  range_eq : φ.range = CFSG.ASVolI.ChH.M24g
  ker_eq : φ.ker = c.E.subgroupOf c.G1
  todd : ↥c.E ≃* W11
  todd_equiv : ∀ (h : ↥c.G1) (e : ↥c.E),
    todd ⟨(h : G) * e * (h : G)⁻¹, c.conj_mem_E h e.2⟩ =
      rho11 AutPerm le_rfl ⟨φ h, φ_mem h⟩ (todd e)

theorem toddCore_nonempty : Nonempty c.ToddCore := by
  classical
  letI : CommGroup ↥c.E := commGroupOfElem c.E_elem
  obtain ⟨e, he⟩ := cocode24_std c.todd
  set ρ := rho11 AutPerm le_rfl with hρ
  have hρinj : Function.Injective ρ := rho11_injective AutPerm le_rfl
  set ψ : ↥c.G1 →* MulAut W11 := (congrHom e).comp (conjNormalizer c.E) with hψ
  have hψmem : ∀ h, ψ h ∈ ρ.range := by
    intro h
    rw [← he]
    exact ⟨conjNormalizer c.E h, ⟨h, rfl⟩, rfl⟩
  set iso := MonoidHom.ofInjective hρinj with hiso
  set φ₀ : ↥c.G1 →* ↥AutPerm :=
    iso.symm.toMonoidHom.comp (ψ.codRestrict ρ.range hψmem) with hφ₀
  have hρφ₀ : ∀ h, ρ (φ₀ h) = ψ h := by
    intro h
    have h1 : iso (φ₀ h) = ψ.codRestrict ρ.range hψmem h := by
      simp [hφ₀]
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  refine ⟨⟨AutPerm.subtype.comp φ₀, fun h => (φ₀ h).2, ?_, ?_, e, ?_⟩⟩
  ·
    apply le_antisymm
    · rintro _ ⟨h, rfl⟩
      exact (φ₀ h).2
    · intro σ hσ
      have hmem : ρ ⟨σ, hσ⟩ ∈ ρ.range := ⟨⟨σ, hσ⟩, rfl⟩
      rw [← he] at hmem
      obtain ⟨_, ⟨h, rfl⟩, hh⟩ := hmem
      refine ⟨h, ?_⟩
      have : ρ (φ₀ h) = ρ ⟨σ, hσ⟩ := by rw [hρφ₀]; exact hh
      have := hρinj this
      show ((φ₀ h : ↥AutPerm) : Equiv.Perm (Fin 24)) = σ
      rw [this]
  ·
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : φ₀ h = 1 := Subtype.ext h1
      have h3 : ψ h = 1 := by rw [← hρφ₀, h2, map_one]
      have h4 : conjNormalizer c.E h = 1 := by
        apply congrHom_injective e
        rw [map_one]
        exact h3
      refine c.centralizer_E (h : G) h.2 fun x hx => ?_
      have h5 := congrArg (fun f : MulAut ↥c.E => ((f ⟨x, hx⟩ : ↥c.E) : G)) h4
      simp only [conjNormalizer_apply, MulAut.one_apply, InvMemClass.coe_inv] at h5
      calc (h : G) * x = (h : G) * x * (h : G)⁻¹ * (h : G) := by group
        _ = x * h := by rw [h5]
    · intro hE
      have h4 : conjNormalizer c.E h = 1 := by
        ext x
        simp only [conjNormalizer_apply, MulAut.one_apply, InvMemClass.coe_inv]
        rw [c.E_comm hE x.2, mul_inv_cancel_right]
      have h3 : ψ h = 1 := by
        show congrHom e (conjNormalizer c.E h) = 1
        rw [h4, map_one]
      have h2 : φ₀ h = 1 := by
        apply hρinj
        rw [hρφ₀, h3, map_one]
      show ((φ₀ h : ↥AutPerm) : Equiv.Perm (Fin 24)) = 1
      rw [h2]
      rfl
  ·
    intro h x
    show e _ = ρ (φ₀ h) (e x)
    rw [hρφ₀]
    show e _ = e ((conjNormalizer c.E h) (e.symm (e x)))
    rw [MulEquiv.symm_apply_apply]
    rfl

end Loc49

end CFSG.Quasithin.H13.AS91
