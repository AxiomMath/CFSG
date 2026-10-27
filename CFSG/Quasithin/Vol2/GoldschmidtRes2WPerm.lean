module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.Res2

open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem mem_kerIn_of_toPermHom_eq_one {X M : Subgroup G} {z : ↥X}
    (hz : MulAction.toPermHom ↥X (↥X ⧸ M.subgroupOf X) z = 1) : (z : G) ∈ kerIn M X := by
  intro c hc
  have h : z • (((⟨c, hc⟩ : ↥X)⁻¹ : ↥X) : ↥X ⧸ M.subgroupOf X) =
      (((⟨c, hc⟩ : ↥X)⁻¹ : ↥X) : ↥X ⧸ M.subgroupOf X) := by
    have := Equiv.Perm.ext_iff.1 hz (((⟨c, hc⟩ : ↥X)⁻¹ : ↥X) : ↥X ⧸ M.subgroupOf X)
    simpa using this
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h
  have h' := (M.subgroupOf X).inv_mem h
  simpa [Subgroup.mem_subgroupOf, mul_assoc] using h'

theorem toPermHom_apply_one_of_mem {X M : Subgroup G} {z : ↥X} (hz : (z : G) ∈ M) :
    MulAction.toPermHom ↥X (↥X ⧸ M.subgroupOf X) z ((1 : ↥X) : ↥X ⧸ M.subgroupOf X) =
      ((1 : ↥X) : ↥X ⧸ M.subgroupOf X) := by
  rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, MulAction.Quotient.smul_mk, smul_eq_mul,
    QuotientGroup.eq]
  simpa [Subgroup.mem_subgroupOf] using M.inv_mem hz

end CFSG.Quasithin.Res2
