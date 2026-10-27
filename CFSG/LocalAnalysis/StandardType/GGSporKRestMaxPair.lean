module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_stabilizer_maximal {G : Type} [Group G] {Ω : Type} [MulAction G Ω] (b : Ω)
    (hs : List G)
    (hcover : ∀ g : G, g • b ≠ b →
      ∃ n ∈ MulAction.stabilizer G b, ∃ h ∈ hs, n • g • b = h • b)
    (hgen : ∀ h ∈ hs, Subgroup.closure ((MulAction.stabilizer G b : Set G) ∪ {h}) = ⊤) :
    ∀ Y : Subgroup G, MulAction.stabilizer G b ≤ Y → Y = MulAction.stabilizer G b ∨ Y = ⊤ := by
  intro Y hNY
  by_contra hcon
  have hYN : Y ≠ MulAction.stabilizer G b := fun h => hcon (Or.inl h)
  have hYtop : Y ≠ ⊤ := fun h => hcon (Or.inr h)
  obtain ⟨y, hyY, hyN⟩ :=
    SetLike.exists_of_lt (lt_of_le_of_ne hNY (fun h => hYN h.symm))
  have hyb : y • b ≠ b := fun hfix => hyN (MulAction.mem_stabilizer_iff.mpr hfix)
  obtain ⟨n, hnN, h, hhhs, hEq⟩ := hcover y hyb
  have hnY : n ∈ Y := hNY hnN
  have hnyY : n * y ∈ Y := Y.mul_mem hnY hyY
  have hz_fix : (h⁻¹ * (n * y)) • b = b := by
    rw [mul_smul, mul_smul, hEq]
    exact inv_smul_eq_iff.mpr rfl
  have hzN : h⁻¹ * (n * y) ∈ MulAction.stabilizer G b :=
    MulAction.mem_stabilizer_iff.mpr hz_fix
  have hzY : h⁻¹ * (n * y) ∈ Y := hNY hzN
  have hinvY : h⁻¹ ∈ Y := by
    have hdec : (h⁻¹ * (n * y)) * (n * y)⁻¹ = h⁻¹ := by
      rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [← hdec]
    exact Y.mul_mem hzY (Y.inv_mem hnyY)
  have hhY : h ∈ Y := by
    simpa using Y.inv_mem hinvY
  have hclos : Subgroup.closure ((MulAction.stabilizer G b : Set G) ∪ {h}) ≤ Y := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_union] at hx
    rcases hx with hx | hx
    · exact hNY hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hhY
  have hYtop' : Y = ⊤ := by
    rw [eq_top_iff, ← hgen h hhhs]
    exact hclos
  exact hYtop hYtop'

end CFSG.StandardType.SporadicShape
