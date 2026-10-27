module

public import Mathlib.GroupTheory.Index

import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

theorem le_of_relIndex_le_two_fpf {G : Type*} [Group G] [Finite G] {E N : Subgroup G}
    [N.Normal] {y : G} (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hy3 : y ^ 3 = 1)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) (hfpf : ∀ e ∈ E, y * e * y⁻¹ = e → e = 1)
    (hidx : N.relIndex E ≤ 2) : E ≤ N := by
  intro e he
  by_contra heN
  have hconj : ∀ g : G, y * g * y⁻¹ ∈ N ↔ g ∈ N := fun g =>
    ⟨fun h => by
      have := Subgroup.Normal.conj_mem inferInstance _ h y⁻¹
      simpa [mul_assoc] using this,
    fun h => Subgroup.Normal.conj_mem inferInstance _ h y⟩
  set H' : Subgroup ↥E := N.subgroupOf E with hH'
  have h1 : H'.index ≠ 1 := by
    intro h
    rw [Subgroup.index_eq_one] at h
    exact heN (by
      have : (⟨e, he⟩ : ↥E) ∈ H' := h ▸ Subgroup.mem_top _
      exact this)
  have h2 : H'.index = 2 := by
    have h0 : H'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle : H'.index ≤ 2 := hidx
    omega
  obtain ⟨e1, he1⟩ : ∃ e1 : G, e1 = y * e * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e2 : G, e2 = y * e1 * y⁻¹ := ⟨_, rfl⟩
  have he1E : e1 ∈ E := he1 ▸ hyE e he
  have he2E : e2 ∈ E := he2 ▸ hyE e1 he1E
  have hN1 : e1 ∉ N := fun h => heN ((hconj e).mp (he1 ▸ h))
  have hN2 : e2 ∉ N := fun h => hN1 ((hconj e1).mp (he2 ▸ h))
  have hyyy : y * y * y = 1 := by simpa [pow_succ] using hy3
  have hfix : y * (e * e1 * e2) * y⁻¹ = e * e1 * e2 := by
    have h3 : y * e2 * y⁻¹ = e := by
      have : y * e2 * y⁻¹ = (y * y * y) * e * (y * y * y)⁻¹ := by
        rw [he2, he1]
        group
      rw [this, hyyy]
      group
    calc y * (e * e1 * e2) * y⁻¹ = (y * e * y⁻¹) * (y * e1 * y⁻¹) * (y * e2 * y⁻¹) := by group
      _ = e1 * e2 * e := by rw [← he1, ← he2, h3]
      _ = e * (e1 * e2) := (hEc e he (e1 * e2) (E.mul_mem he1E he2E)).symm
      _ = e * e1 * e2 := (mul_assoc _ _ _).symm
  have hn1 : e * e1 * e2 = 1 :=
    hfpf _ (E.mul_mem (E.mul_mem he he1E) he2E) hfix
  have key := Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨e, he⟩ : ↥E) * ⟨e1, he1E⟩)
    (b := ⟨e2, he2E⟩)
  have key2 := Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨e, he⟩ : ↥E)) (b := ⟨e1, he1E⟩)
  have hprod : ((⟨e, he⟩ : ↥E) * ⟨e1, he1E⟩) * ⟨e2, he2E⟩ ∈ H' := by
    show e * e1 * e2 ∈ N
    rw [hn1]
    exact N.one_mem
  rw [key] at hprod
  have hA : (⟨e, he⟩ : ↥E) ∉ H' := heN
  have hB : (⟨e1, he1E⟩ : ↥E) ∉ H' := hN1
  have hC : (⟨e2, he2E⟩ : ↥E) ∉ H' := hN2
  have hAB : (⟨e, he⟩ : ↥E) * ⟨e1, he1E⟩ ∈ H' :=
    key2.mpr ⟨fun h => absurd h hA, fun h => absurd h hB⟩
  exact hC (hprod.mp hAB)

end InspW2

end S143

end CFSG.Quasithin
