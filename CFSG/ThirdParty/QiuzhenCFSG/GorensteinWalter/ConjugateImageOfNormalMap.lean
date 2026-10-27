module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Images of conjugate subgroups

If the image of a subgroup under a homomorphism is normal, conjugating the
source subgroup does not change that image.
-/

namespace CFSG.GorensteinWalter

universe u v

/-- A normal subgroup image is unchanged when the source subgroup is
conjugated. -/
public theorem map_conjugateSubgroup_eq_of_map_normal
    {G : Type u} [Group G] {Q : Type v} [Group Q]
    (E : Subgroup G) (f : G →* Q)
    (hnormal : (E.map f).Normal) (g : G) :
    (conjugateSubgroup E g).map f = E.map f := by
  classical
  apply le_antisymm
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨e, he, rfl⟩
    simpa using hnormal.conj_mem (f e)
      (Subgroup.mem_map.mpr ⟨e, he, rfl⟩) (f g)
  · intro y hy
    have hyconj : f g⁻¹ * y * (f g⁻¹)⁻¹ ∈ E.map f :=
      hnormal.conj_mem y hy (f g⁻¹)
    rcases Subgroup.mem_map.mp hyconj with ⟨e, he, heq⟩
    refine Subgroup.mem_map.mpr ⟨g * e * g⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨e, he, by simp [MulAut.conj_apply]⟩
    · rw [map_mul, map_mul, map_inv, heq]
      simp only [map_inv, inv_inv]
      group

end CFSG.GorensteinWalter
