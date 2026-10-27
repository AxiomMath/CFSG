module

public import CFSG.RankThree.PartOne.F106.OddRadAt
import CFSG.SignalizerFunctorTheorem.CatalogBridge.DicksonNonLocal
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift
import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.CatalogBridge (solvable_normal_trivial_of_not_isSolvable_psl2)

theorem solvableRadical_perfectResidual_psl2 {K : Type} [Field K]
    [Finite K] (C : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :
    solvableRadical ↥(perfectResidual ↥C) = ⊥ := by
  classical
  have hDperf : Group.IsPerfect ↥(perfectResidual ↥C) :=
    CFSG.Wreathed.PrimewisePerfectLift.perfectResidual_isPerfect
  let D : Subgroup ↥C := perfectResidual ↥C
  let N : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := D.map C.subtype
  let e : ↥D ≃* ↥N := D.equivMapOfInjective C.subtype C.subtype_injective
  by_cases hN : Group.IsSolvable ↥N
  ·
    have hDs : Group.IsSolvable ↥D := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom)
      e.injective
    have hsub : Subsingleton ↥D := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable ↥D hDs
    exact Subgroup.eq_bot_of_subsingleton _
  ·
    set R : Subgroup ↥N := (solvableRadical ↥D).map e.toMonoidHom with hR
    have hRDn : (solvableRadical ↥D).Normal := CFSG.ABGLocalTools.solvableRadical_normal
    have hRn : R.Normal := Subgroup.Normal.map hRDn e.toMonoidHom e.surjective
    have hRs : Group.IsSolvable ↥R := by
      have := CFSG.ABGLocalTools.solvableRadical_isSolvable (H := ↥D)
      exact Group.isSolvable_of_surjective
        (e.toMonoidHom.subgroupMap_surjective (solvableRadical ↥D))
    have hbot := solvable_normal_trivial_of_not_isSolvable_psl2 N hN R hRs
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hbot

theorem oddRadConcl_psl2 {K : Type} [Field K] [Finite K]
    (β : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :
    OddRadConcl (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) β := by
  unfold OddRadConcl
  rw [solvableRadical_perfectResidual_psl2, Subgroup.card_bot]
  exact odd_one

@[expose] def PslTwo (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, StatedLieAdmissible .PSL 2 2 f ∧ LieModel X .PSL 2 2 f

theorem oddRadAt_pslTwo : OddRadAt PslTwo := by
  intro T _ _ _ ⟨f, _, hmodel⟩ β hβ
  rcases hmodel with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hcl
    let e' : T ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
      e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
    exact oddRadConcl_of_mulEquiv e' (fun β' _ => oddRadConcl_psl2 β') β hβ
  all_goals exact absurd h0 (by norm_num)

end CFSG.RankThree.PartOne.F106
