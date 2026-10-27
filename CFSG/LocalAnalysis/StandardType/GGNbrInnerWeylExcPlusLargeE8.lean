module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusPrimes
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusFrameNoLine
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfSylow
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.RankThree.PartOne.KLCE.CharTwoRep
public import CFSG.RankThree.PartOne.KD4T.Certs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.KD4T

namespace ExcPlusLargeE8

local instance neZeroRankE8 : NeZero Tag.E8.rank := ⟨by decide⟩

@[expose] def moveTableE8 : Fin 8 → Fin 8 × List (Fin Tag.E8.rank) :=
  ![(1, [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7]), (2, [0, 2, 3, 4, 1, 3, 2, 0]),
    (3, [5, 6, 4, 5]), (2, [5, 6, 4, 5]), (5, [5, 6, 4, 5]), (3, [3, 2, 1, 3]),
    (3, [3, 4, 1, 3]), (3, [3, 4, 2, 3])]

theorem moveTableE8_spec : ∀ i : Fin 8, (moveTableE8 i).1 ≠ i ∧
    (moveTableE8 i).2.foldr (reflect .E8) (TableBExcTwo.frameE8Root i) =
      TableBExcTwo.frameE8Root (moveTableE8 i).1 := by
  decide +kernel

section Main


theorem exists_conj_rho_E8 {K : Type} [Field K] [CharP K 2] (i : Fin 8) :
    ∃ j : Fin 8, j ≠ i ∧ ∃ g : adjointGroup .E8 K,
      ∀ A : SL2 K, g * TableBExcTwo.rho K TableBExcTwo.frameE8 i A * g⁻¹ =
        TableBExcTwo.rho K TableBExcTwo.frameE8 j A := by
  obtain ⟨hne, hroot⟩ := moveTableE8_spec i
  refine ⟨(moveTableE8 i).1, hne, ⟨wordRep .E8 K (moveTableE8 i).2, ?_⟩, fun A => ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_adjointGroup k 1
  · apply Subtype.ext
    have h := wordRep_conj_rootSL2 (τ := .E8) (L := K)
      (TableBExcTwo.frameE8.isRoot i) (moveTableE8 i).2 A
    rw [CFSG.LieType.Chevalley.wordProd_smul] at h
    have hroot' : (moveTableE8 i).2.foldr (reflect .E8) (TableBExcTwo.frameE8.root i) =
        TableBExcTwo.frameE8.root (moveTableE8 i).1 := hroot
    rw [hroot'] at h
    simpa [TableBExcTwo.coe_rho] using h

end Main

end ExcPlusLargeE8

section Main


theorem ggTorusNoLine_E8Plus_largePrime {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hlarge : ¬ GGNbrExcPlusSmallPrimeE7E8 p) :
    GGTorusNoLine p 7 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have h3 : p ≠ 3 := fun h => hlarge (Or.inl h)
  have h5 : p ≠ 5 := fun h => hlarge (Or.inr h)
  have h11 : 11 ≤ p :=
    ExcFramesHalf.eleven_le_of_dvd_two_pow_add_one hp hp2 (hK ▸ hpq) h3 h5
  have := TableBExc.finite_recipeGroup .E8 K
  set e := TableBExc.recipeEquiv .E8 K with he_def
  have hT : SylowTorus (TableBExc.RecipeGroup .E8 K) p 8 :=
    (ExcFramesHalf.sylowTorus_E8_half K hp h11 hpq).of_mulEquiv e.symm
  refine ggTorusNoLine_of_scNoLine hp (TableBExc.center_recipeGroup_eq_bot .E8 K)
    (fun φ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ)
    (ExcSplitL.ggCenterPrime_recipe_E8 hp hp2) ?_
  refine ggSCNoLine_of_sylowTorus_frame hp hp2 hpq hT
    (fun i => e.symm.toMonoidHom.comp (TableBExcTwo.rho K TableBExcTwo.frameE8 i))
    (fun i => ?_) (fun i j hij A B => ?_) (fun i => ?_) 7
  · exact e.symm.injective.comp (TableBExcTwo.rho_injective _ i)
  · exact (TableBExcTwo.commute_rho _ hij A B).map e.symm.toMonoidHom
  · obtain ⟨j, hji, g, hg⟩ := ExcPlusLargeE8.exists_conj_rho_E8 (K := K) i
    refine ⟨j, hji, e.symm g, fun A => ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_inv, ← map_mul, hg]

end Main

end CFSG.StandardType

end
