module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

universe u

variable {G : Type u} [Group G]

theorem rightConjugate_subgroupOf_normal (H L : Subgroup G) [L.Normal] (g : G) :
    (rightConjugate H g).subgroupOf L =
      (H.subgroupOf L).map (MulAut.conjNormal (H := L) g⁻¹).toMonoidHom := by
  ext x
  constructor
  · intro hx
    change (x : G) ∈ H.map (MulAut.conj g⁻¹).toMonoidHom at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyL : y ∈ L := by
      have hxL : (x : G) ∈ L := x.property
      have hconj := (inferInstance : L.Normal).conj_mem _ hxL g
      have hyeq : y = g * (x : G) * g⁻¹ := by
        rw [← hyx]
        simp [mul_assoc]
      rw [hyeq]
      exact hconj
    refine Subgroup.mem_map.mpr ⟨⟨y, hyL⟩, hy, ?_⟩
    apply Subtype.ext
    simpa [MulAut.conjNormal_apply] using hyx
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    change (x : G) ∈ H.map (MulAut.conj g⁻¹).toMonoidHom
    refine Subgroup.mem_map.mpr ⟨(y : G), hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa [MulAut.conjNormal_apply] using this

theorem minimalLocalFailure_ambient_right_conjugate [Finite G] {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) (g : G) :
    MinimalInvolutionPointLocalFailure (rightConjugate H g) (rightConjugateElem z g) := by
  refine ⟨local_point_datum_right_conjugate h.local_datum g,
    minimalLocalFailure_central_sylow_right_conjugate h.central_sylow g, ?_, h.smaller⟩
  rw [minimalLocalFailure_conjugate_hull]
  intro hstrong
  apply h.failure
  let L := involutionPointHull z
  let : L.Normal := minimalLocalFailure_hull_normal z
  let e : L ≃* L := MulAut.conjNormal (H := L) g⁻¹
  have hmap := hstrong.map_mulEquiv e.symm
  rw [rightConjugate_subgroupOf_normal H L g] at hmap
  have hid : ((H.subgroupOf L).map e.toMonoidHom).map e.symm.toMonoidHom = H.subgroupOf L := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id (H.subgroupOf L)
    ext x
    simp
  rw [hid] at hmap
  exact hmap

end CFSG.ShultStronglyClosedTI
