module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugateImageOfNormalMap
public import Mathlib.GroupTheory.IsPerfect

namespace CFSG
end CFSG
open CFSG

/-!
# Normality of a component with invariant perfect image

A component is forced to be normal when all of its conjugates have the same
nontrivial perfect image under a homomorphism.  Distinct components commute,
which would make that common image abelian and perfect, hence trivial.
-/

namespace CFSG.GorensteinWalter

universe u v

/-- A component with nontrivial perfect normal image under `f` is normal. -/
public theorem component_normal_of_nontrivial_perfect_normal_image
    {H : Type u} [Group H] [Finite H]
    {Q : Type v} [Group Q]
    (E : Subgroup H) (hE : IsComponentOf E (⊤ : Subgroup H))
    (f : H →* Q)
    (himage_ne : E.map f ≠ ⊥)
    (himage_perfect : Group.IsPerfect (E.map f))
    (himage_normal : (E.map f).Normal) :
    E.Normal := by
  classical
  have hconjImage : ∀ h : H,
      (conjugateSubgroup E h).map f = E.map f :=
    map_conjugateSubgroup_eq_of_map_normal E f himage_normal
  refine ⟨?_⟩
  intro x hx h
  let F : Subgroup H := conjugateSubgroup E h
  have hFcomp : IsComponentOf F (⊤ : Subgroup H) := by
    dsimp [F]
    exact fstar_isComponentOf_conjugateSubgroup_of_mem hE h (by simp)
  have hFE : F = E := by
    by_contra hne
    have hcomm : ⁅F, E⁆ = ⊥ :=
      component_commute_of_ne hFcomp hE hne
    have hmapcomm : ⁅F.map f, E.map f⁆ = ⊥ := by
      rw [← Subgroup.map_commutator]
      rw [hcomm, Subgroup.map_bot]
    have himage_comm : ⁅E.map f, E.map f⁆ = ⊥ := by
      simpa [F, hconjImage h] using hmapcomm
    have himage_self : ⁅E.map f, E.map f⁆ = E.map f :=
      Subgroup.isPerfect_iff.mp himage_perfect
    exact himage_ne (himage_self.symm.trans himage_comm)
  have hxF : h * x * h⁻¹ ∈ F := by
    change h * x * h⁻¹ ∈ E.map (MulAut.conj h).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
  rw [hFE] at hxF
  exact hxF

end CFSG.GorensteinWalter
