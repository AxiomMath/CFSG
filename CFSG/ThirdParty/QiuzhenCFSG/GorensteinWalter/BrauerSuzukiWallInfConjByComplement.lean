module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

/-!
# A complement-intersection calculation for Brauer--Suzuki--Wall

This isolates the elementary subgroup calculation used in paragraph 3.2 of
Bender's Brauer--Suzuki--Wall proof.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

/-- If `M = F ⊔ C`, the subgroup `C` normalizes `F` and lies in a conjugate
of `M`, while `F` is disjoint from that conjugate, then the intersection of
`M` with the conjugate is exactly `C`. -/
public theorem inf_conjBy_eq_complement_of_eq_sup_of_disjoint
    {G : Type*} [Group G]
    (F C M : Subgroup G) (g : G)
    (hM : M = F ⊔ C)
    (hCnormF : C ≤ Subgroup.normalizer (F : Set G))
    (hCMg : C ≤ M.conjBy g)
    (hdisj : Disjoint F (M.conjBy g)) :
    M ⊓ M.conjBy g = C := by
  apply le_antisymm
  · intro z hz
    have hzprod : z ∈ (F : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left F C hCnormF,
        ← hM]
      exact hz.1
    rcases hzprod with ⟨f, hfF, c, hcC, rfl⟩
    have hcMg : c ∈ M.conjBy g := hCMg hcC
    have hfMg : f ∈ M.conjBy g := by
      have hmul := (M.conjBy g).mul_mem hz.2 ((M.conjBy g).inv_mem hcMg)
      simpa [mul_assoc] using hmul
    have hf1 : f = 1 := Subgroup.disjoint_def.mp hdisj hfF hfMg
    simpa [hf1] using hcC
  · intro c hcC
    refine ⟨?_, hCMg hcC⟩
    rw [hM]
    exact Subgroup.mem_sup_right hcC

end CFSG.GorensteinWalter
