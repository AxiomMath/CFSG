module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusPrimes
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusFrameNoLine
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTorus
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcF4TwoTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfSylow
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.RankThree.PartOne.KLCE.CharTwoRep
public import CFSG.RankThree.PartOne.KD4T.Certs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.KD4T

namespace ExcPlusLargeF4

local instance neZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def moveTableF4 : Fin 4 → Fin 4 × List (Fin Tag.F4.rank) :=
  ![(1, [2]), (0, [2]), (1, [3]), (2, [0, 1, 2, 1, 0])]

theorem moveTableF4_spec : ∀ i : Fin 4, (moveTableF4 i).1 ≠ i ∧
    (moveTableF4 i).2.foldr (reflect .F4) (TableBF4Two.orthRoot i) =
      TableBF4Two.orthRoot (moveTableF4 i).1 := by
  decide +kernel

section Main


theorem exists_conj_rho_F4 {K : Type} [Field K] [CharP K 2] (i : Fin 4) :
    ∃ j : Fin 4, j ≠ i ∧ ∃ g : adjointGroup .F4 K,
      ∀ A : SL2 K, g * TableBF4Two.rho K i A * g⁻¹ = TableBF4Two.rho K j A := by
  obtain ⟨hne, hroot⟩ := moveTableF4_spec i
  refine ⟨(moveTableF4 i).1, hne, ⟨wordRep .F4 K (moveTableF4 i).2, ?_⟩, fun A => ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_adjointGroup k 1
  · apply Subtype.ext
    have h := wordRep_conj_rootSL2 (τ := .F4) (L := K) (TableBF4Two.isRoot_orthRoot i)
      (moveTableF4 i).2 A
    rw [CFSG.LieType.Chevalley.wordProd_smul, hroot] at h
    simpa [TableBF4Two.coe_rho] using h

end Main

end ExcPlusLargeF4

section Main


theorem ggTorusNoLine_F4Plus_largePrime {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hlarge : ¬ GGNbrExcPlusSmallPrimeF4 p) :
    GGTorusNoLine p 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  have hp3 : 3 < p := by
    have h2 := hp.two_le
    have h3 : p ≠ 3 := hlarge
    have h4 : p ≠ 4 := fun h => by subst h; exact absurd hp (by norm_num)
    omega
  have := TableBF4.finite_recipeGroup (K := K)
  have he := ExcFramesHalf.orderOf_eq_two_of_dvd_add_one hp hp2 hpq
  set e := TableBF4.recipeEquiv K with he_def
  have hT : SylowTorus (TableBF4.RecipeGroup K) p 4 :=
    (OrdPInnerExc.sylowTorus_F4_two K hp hp3 he).of_mulEquiv e.symm
  refine ggTorusNoLine_of_scNoLine hp (TableBF4.center_recipeGroup_eq_bot K)
    (fun φ hφ _ => TableBF4.idImage_subset_inn K hφ) (ExcSplitL.ggCenterPrime_recipe_F4 hp hp2) ?_
  refine ggSCNoLine_of_sylowTorus_frame hp hp2 hpq hT
    (fun i => e.symm.toMonoidHom.comp (TableBF4Two.rho K i)) (fun i => ?_) (fun i j hij A B => ?_)
    (fun i => ?_) 3
  · exact e.symm.injective.comp (TableBF4Two.rho_injective i)
  · exact (TableBF4Two.commute_rho hij A B).map e.symm.toMonoidHom
  · obtain ⟨j, hji, g, hg⟩ := ExcPlusLargeF4.exists_conj_rho_F4 (K := K) i
    refine ⟨j, hji, e.symm g, fun A => ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_inv, ← map_mul, hg]

end Main

end CFSG.StandardType

end
