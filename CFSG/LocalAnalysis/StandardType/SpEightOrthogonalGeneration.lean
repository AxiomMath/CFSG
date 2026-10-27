module

public import CFSG.LocalAnalysis.StandardType.SpEightTransvections
public import CFSG.Fischer.Classification.Symplectic.OrthoGen
public import CFSG.LieType.Universal.Spin
public import CFSG.LieType.Steinberg.Extras
public import CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.Blueprint.EvenSource

theorem coe_quadPlus_four :
    ⇑(CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)) = Q0 := by
  funext v
  rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
  rfl

section Generation

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem polar_quadPlus_four (u v : Vec) :
    QuadraticMap.polar (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)) u v = omega u v := by
  rw [CFSG.LieType.Universal.Spin.polar_quadPlus, omega_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem tvGL_eq_orthTransvectionGL {w : Vec} (hw : Q0 w = 1) :
    tvGL w = CFSG.Fischer.Classification.orthTransvectionGL
      (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)) w := by
  have hw' : CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2) w = 1 := by
    rw [coe_quadPlus_four]; exact hw
  apply Units.ext
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [tvGL_mulVec, ← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
    CFSG.Fischer.Classification.toLinEquiv_orthTransvectionGL,
    CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hw' (Pi.single i 1),
    polar_quadPlus_four (Pi.single i 1) w]

theorem orthogonalGroup_quadPlus_four_eq_closure_reflect :
    TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)) =
      Subgroup.closure (Set.range (CFSG.ClassicalGroups.Orthogonal.reflect
        (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)))) := by
  have hdim : Module.finrank (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    decide
  refine CFSG.ClassicalGroups.Orthogonal.orthogonalGroup_eq_closure_reflect
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 4 (ZMod 2)) ?_ (Or.inl ?_)
  · rw [hdim]; norm_num
  · rw [hdim]; norm_num

theorem closure_reflect_comap_le_closure_tvGL :
    (Subgroup.closure (Set.range (CFSG.ClassicalGroups.Orthogonal.reflect
        (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2))))).comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv Idx (ZMod 2)).toMonoidHom ≤
      Subgroup.closure {g | ∃ w : Vec, Q0 w = 1 ∧ g = tvGL w} := by
  have key : ∀ H : Subgroup ((Idx → ZMod 2) ≃ₗ[ZMod 2] (Idx → ZMod 2)),
      H.comap (CFSG.ClassicalGroups.Orthogonal.toLinEquiv Idx (ZMod 2)).toMonoidHom =
        H.map (CFSG.ClassicalGroups.Orthogonal.toLinEquiv Idx (ZMod 2)).symm.toMonoidHom :=
    fun H => Subgroup.comap_equiv_eq_map_symm
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv Idx (ZMod 2)) H
  rw [key, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨v : Vec, rfl⟩, rfl⟩
  by_cases hv : CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2) v = 0
  · rw [SetLike.mem_coe, CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hv, map_one]
    exact one_mem _
  · have hv1 : CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2) v = 1 :=
      CFSG.ClassicalGroups.Orthogonal.zmod_two_eq_one_of_ne_zero hv
    have hQ0v : Q0 v = 1 := by rw [← coe_quadPlus_four]; exact hv1
    have heq : (CFSG.ClassicalGroups.Orthogonal.toLinEquiv Idx (ZMod 2)).symm.toMonoidHom
        (CFSG.ClassicalGroups.Orthogonal.reflect
          (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)) v) = tvGL v := by
      rw [MulEquiv.coe_toMonoidHom,
        ← CFSG.Fischer.Classification.toLinEquiv_orthTransvectionGL,
        MulEquiv.symm_apply_apply]
      exact (tvGL_eq_orthTransvectionGL hQ0v).symm
    rw [heq]
    exact Subgroup.subset_closure ⟨v, hQ0v, rfl⟩

end Generation

theorem matrixOrthogonal_eq_closure_tvGL :
    matrixOrthogonal Q0 = Subgroup.closure {g | ∃ w : Vec, Q0 w = 1 ∧ g = tvGL w} := by
  apply le_antisymm
  · intro A hA
    have hL : matrixOrthogonal Q0 =
        (TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2))).comap
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv Idx (ZMod 2)).toMonoidHom := by
      rw [← CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
        (Q := CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)) (Q₀ := Q0) coe_quadPlus_four]
      exact (Subgroup.closure_eq (matrixOrthogonal Q0)).symm
    have hmem : A ∈ (TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2))).comap
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv Idx (ZMod 2)).toMonoidHom := by
      rw [← hL]; exact hA
    rw [Subgroup.mem_comap] at hmem
    rw [orthogonalGroup_quadPlus_four_eq_closure_reflect] at hmem
    exact closure_reflect_comap_le_closure_tvGL (by rwa [Subgroup.mem_comap])
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨w, hw, rfl⟩ := hg
    exact tvGL_mem_matrixOrthogonal hw

end CFSG.StandardType.SpEight
