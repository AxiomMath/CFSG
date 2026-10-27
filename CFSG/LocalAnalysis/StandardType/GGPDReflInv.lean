module

public import CFSG.Mathlib.LinearAlgebra.BilinForm.Reflection
public import Mathlib.LinearAlgebra.BilinearForm.Properties

public section

namespace CFSG.StandardType

theorem ggPD_invariantAlternating_eq_zero {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {I : Type*} (h2 : (2 : k) ≠ 0) (h : I → V) (α : I → Module.Dual k V)
    (hdiag : ∀ i, α i (h i) = 2) (hspan : Submodule.span k (Set.range h) = ⊤)
    (b : LinearMap.BilinForm k V) (hb : b.IsAlt)
    (hinv : ∀ i u v, b (u - α i u • h i) (v - α i v • h i) = b u v) : b = 0 := by
  have hbh : ∀ i, b (h i) = 0 := by
    intro i
    exact LinearMap.BilinMap.apply_left_eq_zero_of_preReflection
      b hb h2 (h i) (α i) (hdiag i) (hinv i)
  have hle : (⊤ : Submodule k V) ≤ b.ker := by
    rw [← hspan]
    exact Submodule.span_le.mpr (by rintro x ⟨i, rfl⟩; exact LinearMap.mem_ker.mpr (hbh i))
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro v
  have hx : b x = 0 := LinearMap.mem_ker.mp (hle Submodule.mem_top)
  rw [hx]
  exact LinearMap.zero_apply v

end CFSG.StandardType

end
