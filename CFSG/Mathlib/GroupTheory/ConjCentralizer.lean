module

public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace Subgroup

theorem map_conj_centralizer_singleton {G : Type*} [Group G] (g z : G) :
    (centralizer {z}).map (MulAut.conj g).toMonoidHom = centralizer {g * z * g⁻¹} := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    exact Commute.map hy (MulAut.conj g)
  · intro hx
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      have h : Commute (g⁻¹ * x * g) z := by
        have hc := (Commute.conj_iff g⁻¹).2 hx
        simpa [mul_assoc] using hc
      exact h
    · simp [MulAut.conj_apply, mul_assoc]

end Subgroup

end
