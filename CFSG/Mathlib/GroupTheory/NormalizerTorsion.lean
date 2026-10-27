module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Bound.Init

public section
namespace Subgroup

variable {G : Type*} [Group G]

theorem mem_normalizer_of_eq_sup_zpowers_of_torsion
    (E H S : Subgroup G) (e : G) (hE : E = H ⊔ zpowers e)
    (heS : e ∈ S) {m : ℕ} (hem : e ^ m = 1)
    (htorsion : ∀ x ∈ S, x ^ m = 1 → x ∈ E)
    {g : G} (hgS : g ∈ normalizer (S : Set G))
    (hgH : g ∈ centralizer (H : Set G)) : g ∈ normalizer (E : Set G) := by
  have hstep (g : G) (hgS : g ∈ normalizer (S : Set G))
      (hgH : g ∈ centralizer (H : Set G)) : E.map (MulAut.conj g) ≤ E := by
    rw [hE, map_sup, MonoidHom.map_zpowers]
    apply sup_le
    · rintro x ⟨h, hh, rfl⟩
      change g * h * g⁻¹ ∈ H ⊔ zpowers e
      have hc := (mem_centralizer_iff.mp hgH h hh).symm
      simpa only [hc, mul_assoc, mul_inv_cancel, mul_one] using
        (mem_sup_left hh : h ∈ H ⊔ zpowers e)
    · apply zpowers_le.mpr
      have hgeS : g * e * g⁻¹ ∈ S := (mem_normalizer_iff.mp hgS e).mp heS
      have hgem : (g * e * g⁻¹) ^ m = 1 := by
        have h := congrArg (MulAut.conj g) hem
        simpa only [map_pow, map_one, MulAut.conj_apply] using h
      rw [← hE]
      exact htorsion _ hgeS hgem
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hstep g hgS hgH
      (show g * x * g⁻¹ ∈ E.map (MulAut.conj g) from ⟨x, hx, rfl⟩)
  · intro hx
    have h := hstep g⁻¹ (inv_mem hgS) (inv_mem hgH)
      (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_assoc, inv_mul_cancel, mul_one] using h

end Subgroup
