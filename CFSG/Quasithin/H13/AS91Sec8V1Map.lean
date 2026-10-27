module

public import CFSG.Quasithin.H13.AS91Sec8V1Defs
public import CFSG.Quasithin.H13.AS91Sec6Base

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Quasithin.H.Mathieu
open CFSG.ASVolI.ChH (M24g S24)
open scoped Pointwise

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem E_le_G3_inf_G1 : c.E ≤ c.G3 ⊓ c.G1 := le_inf c.E_le_G3 c.E_le_G1

theorem φ_mem_sextStab (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0) (h : ↥(c.G3 ⊓ c.G1)) :
    r.φ (Subgroup.inclusion inf_le_right h) ∈ M24G.sextStab := by
  refine Subgroup.mem_inf.mpr ⟨r.toResM24.φ_mem _, ?_⟩
  rw [MulAction.mem_stabilizer_iff, ← hU]
  exact (r.stab₃ _).mp (Subgroup.mem_inf.mp h.2).1

@[expose] noncomputable def phiS (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0) :
    ↥(c.G3 ⊓ c.G1) →* ↥M24G.sextStab :=
  (r.φ.comp (Subgroup.inclusion inf_le_right)).codRestrict M24G.sextStab
    (c.φ_mem_sextStab r hU)

@[simp] theorem coe_phiS (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0) (h : ↥(c.G3 ⊓ c.G1)) :
    ((c.phiS r hU h : ↥M24G.sextStab) : S24) = r.φ (Subgroup.inclusion inf_le_right h) :=
  rfl

theorem phiS_surjective (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0) :
    Function.Surjective (c.phiS r hU) := by
  intro s
  obtain ⟨h, hh⟩ := r.toResM24.exists_φ_eq (Subgroup.mem_inf.mp s.2).1
  have hG3 : (h : G) ∈ c.G3 := by
    rw [r.stab₃ h, hh, hU]
    exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp s.2).2
  refine ⟨⟨h, Subgroup.mem_inf.mpr ⟨hG3, h.2⟩⟩, Subtype.ext ?_⟩
  rw [coe_phiS]
  exact hh

theorem phiS_eq_one_iff (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0) (h : ↥(c.G3 ⊓ c.G1)) :
    c.phiS r hU h = 1 ↔ (h : G) ∈ c.E := by
  rw [← Subtype.coe_inj, coe_phiS, OneMemClass.coe_one, ← MonoidHom.mem_ker, r.ker_eq,
    Subgroup.mem_subgroupOf]
  rfl

theorem rho11_sextStab_apply (s : ↥M24G.sextStab) (w : W11) :
    rho11 M24G.sextStab M24G.sextStab_le s w =
      rho11 CFSG.Monster.Code.AutPerm le_rfl ⟨s, M24G.sextStab_le s.2⟩ w :=
  rfl

theorem todd_conj_phiS (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0) (h : ↥(c.G3 ⊓ c.G1))
    (e : ↥c.E) :
    r.todd ⟨(h : G) * e * (h : G)⁻¹, c.conj_mem_E (Subgroup.inclusion inf_le_right h) e.2⟩ =
      rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h) (r.todd e) :=
  r.todd_equiv (Subgroup.inclusion inf_le_right h) e

theorem exists_resM24T_sextFin_zero (r : ResM24T c) :
    ∃ r' : ResM24T c, r'.U₀ = M24G.sextFin 0 :=
  ResM24T.exists_U₀_eq r (M24G.isSextet_sextFin (by norm_num))

@[expose] def IsInnerCocycle (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1)) : Prop :=
  ∃ (g : G) (D : ↥M24G.sextStab → W11), g ∈ c.G3 ⊓ c.G1 ∧
    M24G.IsRightCocycle M24G.sextStab M24G.sextStab_le D ∧
    ∀ h : ↥(c.G3 ⊓ c.G1), ((θ h : ↥(c.G3 ⊓ c.G1)) : G) =
      g * ((h : G) * (r.todd.symm (D (c.phiS r hU h)) : G)) * g⁻¹

@[expose] def HasAlphaTwist (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0) : Prop :=
  ∃ (χ : ↥M24G.sextStab →* Multiplicative (ZMod 2)) (α : ↥c.G3 ≃* ↥c.G3), χ ≠ 1 ∧
    (∀ h : ↥c.G3, (h : G) ∈ c.G1 ↔ ((α h : ↥c.G3) : G) ∈ c.G1) ∧
    ∀ h : ↥(c.G3 ⊓ c.G1), ((α (Subgroup.inclusion inf_le_left h) : ↥c.G3) : G) =
      (h : G) * (r.todd.symm
        (if χ (c.phiS r hU h) = 1 then 1 else M24G.sextClass (M24G.sextFin 0)) : G)

@[expose] def HasBetaTwist (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0) : Prop :=
  ∃ β : ↥c.G1 ≃* ↥c.G1,
    (∀ m : ↥c.G1, (m : G) ∈ c.G3 ↔ ((β m : ↥c.G1) : G) ∈ c.G3) ∧
    ∀ h : ↥(c.G3 ⊓ c.G1), ((β (Subgroup.inclusion inf_le_right h) : ↥c.G1) : G) =
      (h : G) * (r.todd.symm (M24G.dBeta M24G.sextStab (c.phiS r hU h)) : G)

end Loc49

end CFSG.Quasithin.H13.AS91
