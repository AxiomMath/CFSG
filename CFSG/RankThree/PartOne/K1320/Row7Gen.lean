module

public import CFSG.RankThree.PartOne.KF.R7Levi2
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot

public section

namespace CFSG.RankThree.PartOne.K1320

open Matrix CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat elt)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem shortBlock_sup_longBlock_zero_eq_top :
    (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range ⊔ (longBlock K 2 0).range = ⊤ := by
  set H' : Subgroup (StatedSp 2 K) :=
    (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range ⊔ (longBlock K 2 0).range with hH'
  have hS : ∀ c : K, elt (.difference 0 1 zero_ne_one) c ∈ H' := fun c =>
    Subgroup.mem_sup_left ⟨sl2Upper c, shortBlock_sl2Upper _ c⟩
  have hS' : ∀ c : K, elt (.difference 1 0 zero_ne_one.symm) c ∈ H' := fun c =>
    Subgroup.mem_sup_left ⟨sl2Lower c, shortBlock_sl2Lower _ c⟩
  have hL : ∀ c : K, elt (.positiveLong 0) c ∈ H' := fun c =>
    Subgroup.mem_sup_right ⟨sl2Upper c, longBlock_sl2Upper 0 c⟩
  have hL' : ∀ c : K, elt (.negativeLong 0) c ∈ H' := fun c =>
    Subgroup.mem_sup_right ⟨sl2Lower c, longBlock_sl2Lower 0 c⟩
  let H : Subgroup (TauCeti.GLSymplecticFin 2 K) := H'.comap (equivStatedSp 2 K).toMonoidHom
  have hH : H = ⊤ := by
    refine TauCeti.GLSymplecticFin.eq_top_of_adjacent_of_long H 0 ?_ ?_ ?_
    · intro i j hij c hadj
      have key : equivStatedSp 2 K (TauCeti.GLSymplecticFin.differenceShortRootUnit hij c) =
          elt (.difference i j hij) c := by
        simp only [elt, TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_difference,
          TauCeti.GLSymplecticFin.differenceShortRootHom_apply, toAdd_ofAdd]
      change equivStatedSp 2 K _ ∈ H'
      rw [key]
      have hi := i.isLt
      have hj := j.isLt
      have hcase : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
        rcases hadj with h | h
        · exact Or.inl ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
        · exact Or.inr ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hS c
      · exact hS' c
    · intro c
      have key : equivStatedSp 2 K
          (TauCeti.GLSymplecticFin.positiveLongRootTransvectionUnit 0 c) =
          elt (.positiveLong 0) c := by
        simp only [elt, TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_positiveLong,
          TauCeti.GLSymplecticFin.positiveLongRootTransvectionHom_apply, toAdd_ofAdd]
      change equivStatedSp 2 K _ ∈ H'
      rw [key]
      exact hL c
    · intro c
      have key : equivStatedSp 2 K
          (TauCeti.GLSymplecticFin.negativeLongRootTransvectionUnit 0 c) =
          elt (.negativeLong 0) c := by
        simp only [elt, TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_negativeLong,
          TauCeti.GLSymplecticFin.negativeLongRootTransvectionHom_apply, toAdd_ofAdd]
      change equivStatedSp 2 K _ ∈ H'
      rw [key]
      exact hL' c
  rw [eq_top_iff]
  intro x _
  have : (equivStatedSp 2 K).symm x ∈ H := hH ▸ Subgroup.mem_top _
  simpa [H] using this

theorem spRevEquiv_longBlock [CharP K 2] (A : SL(2, K)) :
    spRevEquiv K (longBlock K 2 0 A) = spBlock A := by
  apply Subtype.ext
  apply Units.ext
  have h1 : (((spRevEquiv K (longBlock K 2 0 A) : ↥(spRev K)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) =
      (mat 2 K (longBlock K 2 0 A)).submatrix spIdx.symm spIdx.symm :=
    coe_reindexGL' spIdx _
  rw [h1, mat_longBlock]
  change _ = blk22 (A : Matrix (Fin 2) (Fin 2) K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.LieType.Steinberg.Sp.blockMat, blk22, spIdx, Matrix.one_apply]

theorem spRevEquiv_shortBlock [CharP K 2] (A : SL(2, K)) :
    spRevEquiv K (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) A) = spBlock' A := by
  apply Subtype.ext
  apply Units.ext
  have h1 : (((spRevEquiv K (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) A) : ↥(spRev K)) :
      GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (mat 2 K (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) A)).submatrix spIdx.symm
        spIdx.symm := coe_reindexGL' spIdx _
  rw [h1, mat_shortBlock]
  change _ = blk4 (A : Matrix (Fin 2) (Fin 2) K)
  have h3 : ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      adjugate (A : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.LieType.Steinberg.Sp.blockMat, blk4, spIdx, Matrix.one_apply, Matrix.fromBlocks,
      h3, Matrix.adjugate_fin_two, Matrix.transpose_apply]
  all_goals exact CharTwo.neg_eq _

theorem spBlock_sup_spBlock'_eq_top [CharP K 2] :
    (spBlock (K := K)).range ⊔ (spBlock' (K := K)).range = ⊤ := by
  have h := shortBlock_sup_longBlock_zero_eq_top (K := K)
  have e1 : ((spRevEquiv K).toMonoidHom.comp (longBlock K 2 0)) = spBlock :=
    MonoidHom.ext fun A => spRevEquiv_longBlock A
  have e2 : ((spRevEquiv K).toMonoidHom.comp (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1))) =
      spBlock' :=
    MonoidHom.ext fun A => spRevEquiv_shortBlock A
  rw [← e1, ← e2, MonoidHom.range_comp, MonoidHom.range_comp, ← Subgroup.map_sup, sup_comm, h,
    ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr (spRevEquiv K).surjective

end CFSG.RankThree.PartOne.K1320
