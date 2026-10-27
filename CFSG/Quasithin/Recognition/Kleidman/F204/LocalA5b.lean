module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalA5

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Quasithin.H.A5W CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem klein_trans_perm : ∀ a b : Fin 5, a ≠ 4 → b ≠ 4 →
    ∃ k : Perm (Fin 5), Perm.sign k = 1 ∧ k ∈ kleinSet ∧ k a = b := by
  decide +kernel

theorem alt5_klein_trans {T : Subgroup Alt5} (hT : Nat.card T = 4) {x y : Alt5}
    (hx : x ∉ Subgroup.normalizer (T : Set Alt5)) (hy : y ∉ Subgroup.normalizer (T : Set Alt5)) :
    ∃ k ∈ T, y⁻¹ * k * x ∈ Subgroup.normalizer (T : Set Alt5) := by
  obtain ⟨g, hg⟩ := exists_conj_kleinStd T hT
  have hN : ∀ z : Alt5, z ∈ Subgroup.normalizer (T : Set Alt5) ↔
      g⁻¹ * z * g ∈ Subgroup.normalizer (kleinStd : Set Alt5) := by
    intro z
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h k
      have := h (g * k * g⁻¹)
      rw [hg, hg] at this
      have e : g⁻¹ * (g * k * g⁻¹) * g = k := by group
      have e2 : g⁻¹ * (z * (g * k * g⁻¹) * z⁻¹) * g = (g⁻¹ * z * g) * k * (g⁻¹ * z * g)⁻¹ := by
        group
      rwa [e, e2] at this
    · intro h k
      have := h (g⁻¹ * k * g)
      rw [hg, hg]
      have e2 : g⁻¹ * (z * k * z⁻¹) * g = (g⁻¹ * z * g) * (g⁻¹ * k * g) * (g⁻¹ * z * g)⁻¹ := by
        group
      rwa [e2]
  set x' : Alt5 := g⁻¹ * x * g with hx'
  set y' : Alt5 := g⁻¹ * y * g with hy'
  have hx4 : (x' : Perm (Fin 5)) 4 ≠ 4 := by
    exact fun h => hx ((hN x).mpr ((mem_normalizer_kleinStd x').mpr h))
  have hy4 : (y' : Perm (Fin 5)) 4 ≠ 4 := by
    exact fun h => hy ((hN y).mpr ((mem_normalizer_kleinStd y').mpr h))
  obtain ⟨k', hs, hk', hka⟩ := klein_trans_perm ((x' : Perm (Fin 5)) 4) ((y' : Perm (Fin 5)) 4)
    hx4 hy4
  set k'' : Alt5 := ⟨k', Perm.mem_alternatingGroup.mpr hs⟩ with hk''
  refine ⟨g * k'' * g⁻¹, ?_, ?_⟩
  · rw [hg]
    have : g⁻¹ * (g * k'' * g⁻¹) * g = k'' := by group
    rw [this]; exact hk'
  · rw [hN, mem_normalizer_kleinStd]
    have e : g⁻¹ * (y⁻¹ * (g * k'' * g⁻¹) * x) * g = y'⁻¹ * k'' * x' := by
      rw [hx', hy']; group
    rw [e]
    show (y'⁻¹ * k'' * x' : Alt5).1 4 = 4
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
    rw [Perm.inv_eq_iff_eq]
    exact hka

end CFSG.Quasithin.Kleidman.F204
