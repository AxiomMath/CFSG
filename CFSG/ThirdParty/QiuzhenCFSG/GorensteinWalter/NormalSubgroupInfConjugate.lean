module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Normal subgroups in intersections with conjugates -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A subgroup normal in `H` and contained in `M` lies in the intersection of
`M` with every conjugate `M^y` represented by an element `y ∈ H`. -/
public theorem normalSubgroup_le_inf_conjugateSubgroup
    {G : Type u} [Group G]
    {N H M : Subgroup G} {y : G}
    (hNnormal : IsNormalIn N H) (hNleM : N ≤ M) (hyH : y ∈ H) :
    N ≤ M ⊓ conjugateSubgroup M y := by
  intro x hx
  refine ⟨hNleM hx, ?_⟩
  change x ∈ M.map (MulAut.conj y).toMonoidHom
  let x0 := y⁻¹ * x * y
  have hx0N : x0 ∈ N := by
    simpa [x0] using hNnormal.2 y⁻¹ (H.inv_mem hyH) x hx
  refine Subgroup.mem_map.mpr ⟨x0, hNleM hx0N, ?_⟩
  dsimp [x0]
  group

end CFSG.GorensteinWalter
