module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Walter.W67

namespace JRBasic

open scoped Pointwise

variable {G : Type*} [Group G]

theorem mem_conj_smul_iff'' {H : Subgroup G} {g x : G} :
    x ∈ MulAut.conj g • H ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply, inv_inv]

theorem centralizer_conj_smul (g : G) (H : Subgroup G) :
    Subgroup.centralizer ((MulAut.conj g • H : Subgroup G) : Set G) =
      MulAut.conj g • Subgroup.centralizer (H : Set G) := by
  ext x
  rw [mem_conj_smul_iff'', Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    have := hx (g * y * g⁻¹) (by rw [SetLike.mem_coe, mem_conj_smul_iff'']; simpa [mul_assoc])
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * x * g * y := by group
  · intro hx y hy
    rw [SetLike.mem_coe, mem_conj_smul_iff''] at hy
    have := hx _ hy
    calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = x * y := by group

theorem normalizer_conj_smul (g : G) (H : Subgroup G) :
    Subgroup.normalizer ((MulAut.conj g • H : Subgroup G) : Set G) =
      MulAut.conj g • Subgroup.normalizer (H : Set G) := by
  ext n
  rw [mem_conj_smul_iff'', Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hn y
    have := hn (g * y * g⁻¹)
    rw [mem_conj_smul_iff'', mem_conj_smul_iff''] at this
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group,
      show g⁻¹ * (n * (g * y * g⁻¹) * n⁻¹) * g = g⁻¹ * n * g * y * (g⁻¹ * n * g)⁻¹ by group]
      at this
  · intro hn y
    rw [mem_conj_smul_iff'', mem_conj_smul_iff'']
    have := hn (g⁻¹ * y * g)
    rwa [show g⁻¹ * n * g * (g⁻¹ * y * g) * (g⁻¹ * n * g)⁻¹ = g⁻¹ * (n * y * n⁻¹) * g by group]
      at this

theorem card_conj_smul' (g : G) (H : Subgroup G) :
    Nat.card (MulAut.conj g • H : Subgroup G) = Nat.card H :=
  (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) H).toEquiv).symm

theorem exists_conj_sylow [Finite G] {p : ℕ} [Fact p.Prime] (P Q : Sylow p G) :
    ∃ g : G, (Q : Subgroup G) = MulAut.conj g • (P : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  exact ⟨g, by rw [← hg, Sylow.coe_subgroup_smul]⟩

end JRBasic

end CFSG.Walter.W67
