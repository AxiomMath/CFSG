module

public import CFSG.Quasithin.H13.AS91Sec5ResM24T

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace ResM24T

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z}

theorem map_conj_M24g {σ : S24} (hσ : σ ∈ M24g) :
    M24g.map (MulAut.conj σ).toMonoidHom = M24g :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hσ)

@[expose] noncomputable def conjBy (r : ResM24T c) {σ : S24} (hσ : σ ∈ M24g) : ResM24T c where
  φ := (MulAut.conj σ).toMonoidHom.comp r.φ
  range_eq := by
    rw [MonoidHom.range_comp, r.range_eq]
    exact map_conj_M24g hσ
  ker_eq := by
    rw [← r.ker_eq]
    ext h
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro h1
      have : r.φ h = σ⁻¹ * (σ * r.φ h * σ⁻¹) * σ := by group
      rw [this, h1]
      group
    · intro h1
      rw [h1]
      group
  l₀ := σ • r.l₀
  U₀ := σ • r.U₀
  isTrio_l₀ := (M24G.isTrio_smul_iff hσ).2 r.isTrio_l₀
  isSextet_U₀ := (M24G.isSextet_smul_iff hσ).2 r.isSextet_U₀
  trioIn_l₀_U₀ := (M24G.trioIn_smul_iff σ).2 r.trioIn_l₀_U₀
  stab₂ := fun h => by
    rw [r.stab₂ h]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, mul_smul, inv_smul_smul]
    exact (smul_left_cancel_iff σ).symm
  stab₃ := fun h => by
    rw [r.stab₃ h]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, mul_smul, inv_smul_smul]
    exact (smul_left_cancel_iff σ).symm
  todd := r.todd.trans (rho11 AutPerm le_rfl ⟨σ, hσ⟩)
  todd_equiv := fun h e => by
    simp only [MulEquiv.trans_apply]
    rw [r.todd_equiv h e]
    have hmul : (⟨σ * r.φ h * σ⁻¹, by
        have := (r.toResM24.φ_mem h)
        exact M24g.mul_mem (M24g.mul_mem hσ this) (M24g.inv_mem hσ)⟩ : ↥AutPerm) *
          ⟨σ, hσ⟩ = ⟨σ, hσ⟩ * ⟨r.φ h, r.toResM24.φ_mem h⟩ := by
      apply Subtype.ext
      show σ * r.φ h * σ⁻¹ * σ = σ * r.φ h
      group
    have key := congrArg (fun a => rho11 AutPerm le_rfl a (r.todd e)) hmul
    simp only [map_mul, MulAut.mul_apply] at key
    exact key.symm

@[simp] theorem conjBy_U₀ (r : ResM24T c) {σ : S24} (hσ : σ ∈ M24g) :
    (r.conjBy hσ).U₀ = σ • r.U₀ := rfl

@[simp] theorem conjBy_l₀ (r : ResM24T c) {σ : S24} (hσ : σ ∈ M24g) :
    (r.conjBy hσ).l₀ = σ • r.l₀ := rfl

theorem exists_U₀_eq (r : ResM24T c)
    {U : Finset (Finset (Fin 24))} (hU : IsSextet U) :
    ∃ r' : ResM24T c, r'.U₀ = U := by
  obtain ⟨a, ha, haU⟩ := M24G.sextet_transitive r.isSextet_U₀
  obtain ⟨b, hb, hbU⟩ := M24G.sextet_transitive hU
  have hσ : b⁻¹ * a ∈ M24g := M24g.mul_mem (M24g.inv_mem hb) ha
  refine ⟨r.conjBy hσ, ?_⟩
  rw [conjBy_U₀, mul_smul, haU, ← hbU, inv_smul_smul]

@[expose] def toToddCore (r : ResM24T c) : c.ToddCore :=
  ⟨r.φ, r.toResM24.φ_mem, r.range_eq, r.ker_eq, r.todd, r.todd_equiv⟩

theorem todd_z
    (r : ResM24T c) :
    r.todd ⟨z, c.z_mem_E⟩ = M24G.sextClass r.U₀ := by
  set P : Subgroup S24 := ((c.T : Subgroup G).subgroupOf c.G1).map r.φ with hP
  have hPle : P ≤ M24g := by
    rw [hP, ← r.range_eq]
    exact Subgroup.map_le_range _ _
  have hPcard : Nat.card P = 2 ^ 10 := c.card_map_T r.toToddCore
  obtain ⟨U, -, hfix⟩ := M24G.fix_sylow P hPle hPcard
  have hmemP : ∀ σ ∈ P, ∃ t : ↥c.G1, (t : G) ∈ (c.T : Subgroup G) ∧ r.φ t = σ := by
    intro σ hσ
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hσ
    exact ⟨t, Subgroup.mem_subgroupOf.mp ht, rfl⟩
  have hz1 : z ≠ 1 := fun h => c.S.z_ne_one (c.S_z.trans h)
  have hez1 : r.todd ⟨z, c.z_mem_E⟩ ≠ 1 := by
    intro h
    apply hz1
    have h' : (⟨z, c.z_mem_E⟩ : ↥c.E) = 1 := r.todd.injective (h.trans (map_one r.todd).symm)
    exact congrArg Subtype.val h'
  have hfz : ∀ (σ : S24) (hσ : σ ∈ P),
      rho11 AutPerm le_rfl ⟨σ, hPle hσ⟩ (r.todd ⟨z, c.z_mem_E⟩) = r.todd ⟨z, c.z_mem_E⟩ := by
    intro σ hσ
    obtain ⟨t, ht, rfl⟩ := hmemP σ hσ
    show rho11 AutPerm le_rfl ⟨r.φ t, r.toResM24.φ_mem t⟩ (r.todd ⟨z, c.z_mem_E⟩) = _
    rw [← r.todd_equiv t ⟨z, c.z_mem_E⟩]
    congr 1
    apply Subtype.ext
    simpa using c.G3_comm_z (inv_mem (c.T_le_G3 ht))
  have hfU : ∀ (σ : S24) (hσ : σ ∈ P),
      rho11 AutPerm le_rfl ⟨σ, hPle hσ⟩ (M24G.sextClass r.U₀) = M24G.sextClass r.U₀ := by
    intro σ hσ
    obtain ⟨t, ht, rfl⟩ := hmemP σ hσ
    show rho11 AutPerm le_rfl ⟨r.φ t, r.toResM24.φ_mem t⟩ (M24G.sextClass r.U₀) = _
    rw [← M24G.sextClass_smul (r.toResM24.φ_mem t) r.isSextet_U₀,
      (r.stab₃ t).mp (c.T_le_G3 ht)]
  have hU1 : M24G.sextClass r.U₀ ≠ 1 := M24G.sextClass_ne_one r.isSextet_U₀
  rw [((hfix _).1 hfz).resolve_left hez1, ((hfix _).1 hfU).resolve_left hU1]

end ResM24T

end CFSG.Quasithin.H13.AS91
