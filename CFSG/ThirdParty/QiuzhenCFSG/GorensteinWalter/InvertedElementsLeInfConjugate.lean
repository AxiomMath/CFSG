module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Inverted elements lie in a conjugate intersection -/

namespace CFSG.GorensteinWalter

universe u

/-- Every element of `M` inverted by `y` lies in `M ∩ M^y`. -/
public theorem invertedElements_subset_inf_conjugateSubgroup
    {G : Type u} [Group G] (M : Subgroup G) (y : G) :
    invertedElements M y ⊆
      (M ⊓ conjugateSubgroup M y : Subgroup G) := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  change x ∈ M.map (MulAut.conj y).toMonoidHom
  apply Subgroup.mem_map.mpr
  refine ⟨x⁻¹, M.inv_mem hx.1, ?_⟩
  change y * x⁻¹ * y⁻¹ = x
  calc
    y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ := by group
    _ = (x⁻¹)⁻¹ := by rw [hx.2]
    _ = x := by simp

end CFSG.GorensteinWalter
