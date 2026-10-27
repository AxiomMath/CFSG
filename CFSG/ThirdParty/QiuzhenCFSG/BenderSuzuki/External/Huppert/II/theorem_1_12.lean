module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert II.1.12(b)

The double-coset decomposition of a doubly transitive permutation group with
respect to a point stabilizer.
-/

namespace CFSG.BenderSuzuki
namespace External

universe u v

/-- Huppert II.1.12(b): a doubly transitive group has two point-stabilizer
double cosets. -/
public theorem huppert_II_1_12_b_doubleCoset_decomposition
    {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω]
    (h2 : MulAction.IsMultiplyPretransitive G Ω 2)
    (a : Ω) (t : G) (ht : t • a ≠ a) :
    ((MulAction.stabilizer G a : Set G) ∪
      DoubleCoset.doubleCoset t (MulAction.stabilizer G a)
        (MulAction.stabilizer G a)) = Set.univ := by
  ext g
  simp only [Set.mem_union, SetLike.mem_coe, Set.mem_univ, iff_true]
  by_cases hg : g • a = a
  · exact Or.inl hg
  · right
    rw [MulAction.is_two_pretransitive_iff] at h2
    obtain ⟨x, hxt, hxa⟩ := h2 ht hg
    have hx : x ∈ MulAction.stabilizer G a := hxa
    have hx_inv : x⁻¹ • (g • a) = t • a := by
      rw [← hxt, inv_smul_smul]
    have hy : t⁻¹ * x⁻¹ * g ∈ MulAction.stabilizer G a := by
      change (t⁻¹ * x⁻¹ * g) • a = a
      simp only [mul_smul]
      rw [hx_inv, inv_smul_smul]
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨x, hx, t⁻¹ * x⁻¹ * g, hy, by group⟩

end External
end CFSG.BenderSuzuki
