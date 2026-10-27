module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.RankThree.PartOne.CTP.SpEven

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem spMat_longBlock (A : SL(2, K)) :
    spMat (longBlock K 2 1 A) =
      blockMat (Sum.inl 1) (Sum.inr 1) (A : Matrix (Fin 2) (Fin 2) K) :=
  mat_longBlock 1 A

theorem exceptionalSpAut_longBlock [Finite K] [CharP K 2] (A : SL(2, K)) :
    exceptionalSpAut K (longBlock K 2 1 A) = shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) A := by
  have hS : spMat (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) A) =
      fromBlocks (blockMat (0 : Fin 2) 1 (A : Matrix (Fin 2) (Fin 2) K)) 0 0
        (blockMat (0 : Fin 2) 1 ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))ᵀ :=
    mat_shortBlock _ A
  refine Subtype.ext (Units.ext ?_)
  change spMat (exceptionalSpAut K _) = spMat (shortBlock K _ A)
  rw [spMat_exceptionalSpAut', spMat_longBlock, hS, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  ext p q
  rcases p with p | p <;> rcases q with q | q <;> fin_cases p <;> fin_cases q <;>
    simp [blockMat, minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two,
      minorIdx_three, antiIdx_inl_zero, antiIdx_inl_one, antiIdx_inr_zero, antiIdx_inr_one,
      antiIdx_symm_zero, antiIdx_symm_one, antiIdx_symm_two, antiIdx_symm_three, CharTwo.neg_eq]

theorem exists_frobenius_equiv [Finite K] [CharP K 2] : ∃ Fr : K ≃+* K, ∀ x, Fr x = x ^ 2 := by
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  exact ⟨frobeniusEquiv K 2, fun x => rfl⟩

theorem blockMat_map_ringHom {κ : Type*} [DecidableEq κ] {L : Type} [Field L] (p q : κ)
    (A : Matrix (Fin 2) (Fin 2) K) (f : K →+* L) :
    (blockMat p q A).map f = blockMat p q (A.map f) := by
  ext a b
  simp only [Matrix.map_apply, blockMat, Matrix.of_apply]
  split_ifs <;> simp [Matrix.one_apply, *]

theorem fieldSp_longBlock (Fr : K ≃+* K) (A : SL(2, K)) :
    fieldSp 2 K Fr (longBlock K 2 1 A) =
      longBlock K 2 1 (Matrix.SpecialLinearGroup.map Fr.toRingHom A) := by
  refine Subtype.ext (Units.ext ?_)
  change (spMat (longBlock K 2 1 A)).map Fr =
    spMat (longBlock K 2 1 (Matrix.SpecialLinearGroup.map Fr.toRingHom A))
  rw [spMat_longBlock, spMat_longBlock]
  exact blockMat_map_ringHom _ _ _ Fr.toRingHom

theorem exceptionalSpAut_shortBlock [Finite K] [CharP K 2] {Fr : K ≃+* K}
    (hFr : ∀ x, Fr x = x ^ 2) (A : SL(2, K)) :
    exceptionalSpAut K (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) A) =
      longBlock K 2 1 (Matrix.SpecialLinearGroup.map Fr.toRingHom A) := by
  rw [← exceptionalSpAut_longBlock A, exceptionalSpAut_sq hFr, fieldSp_longBlock]

theorem specialLinearGroup_map_bijective (Fr : K ≃+* K) :
    Function.Bijective (Matrix.SpecialLinearGroup.map (n := Fin 2) Fr.toRingHom) :=
  ⟨fun A B h => by
    have := congrArg (Matrix.SpecialLinearGroup.map (n := Fin 2) Fr.symm.toRingHom) h
    rwa [CFSG.ClassicalInvolution.WeakCT.map_map_symm,
      CFSG.ClassicalInvolution.WeakCT.map_map_symm] at this,
    fun B => ⟨Matrix.SpecialLinearGroup.map Fr.symm.toRingHom B,
      CFSG.ClassicalInvolution.WeakCT.map_symm_map Fr B⟩⟩

theorem map_exceptionalSpAut_range_longBlock [Finite K] [CharP K 2] :
    (longBlock K 2 1).range.map (exceptionalSpAut K).toMonoidHom =
      (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range := by
  have hcomp : (exceptionalSpAut K).toMonoidHom.comp (longBlock K 2 1) =
      shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) :=
    MonoidHom.ext fun A => exceptionalSpAut_longBlock A
  rw [← MonoidHom.range_comp, hcomp]

theorem map_exceptionalSpAut_range_shortBlock [Finite K] [CharP K 2] :
    (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map (exceptionalSpAut K).toMonoidHom =
      (longBlock K 2 1).range := by
  obtain ⟨Fr, hFr⟩ := exists_frobenius_equiv (K := K)
  have hcomp : (exceptionalSpAut K).toMonoidHom.comp
      (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)) =
      (longBlock K 2 1).comp (Matrix.SpecialLinearGroup.map (n := Fin 2) Fr.toRingHom) :=
    MonoidHom.ext fun A => exceptionalSpAut_shortBlock hFr A
  rw [← MonoidHom.range_comp, hcomp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (specialLinearGroup_map_bijective Fr).2, ← MonoidHom.range_eq_map]

theorem symplecticBlockStandardPair_swap [Finite K] [CharP K 2] {X : Type} [Group X]
    {W U V : Subgroup X} (h : SymplecticBlockStandardPair K W U V) :
    SymplecticBlockStandardPair K W V U := by
  obtain ⟨θ, c, hW, hker, hinjL, hinjS, hU, hV⟩ := h
  obtain ⟨Fr, hFr⟩ := exists_frobenius_equiv (K := K)
  let γ : StatedSp 2 K →* StatedSp 2 K := (exceptionalSpAut K).toMonoidHom
  let α : StatedSp 2 K →* StatedSp 2 K := (MulAut.conj c⁻¹).toMonoidHom.comp γ
  have hα : Function.Bijective α :=
    ((exceptionalSpAut K).trans (MulAut.conj c⁻¹)).bijective
  have hcen : Subgroup.center (StatedSp 2 K) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    exact Subgroup.mem_bot.mpr (center_sp_eq_one_of_charTwo hg)
  have hθker : θ.ker = ⊥ := by
    rw [eq_bot_iff]
    exact hker.trans hcen.le
  have hθinj : Function.Injective θ := (MonoidHom.ker_eq_bot_iff θ).mp hθker
  refine ⟨θ.comp α, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hW]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨α y, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := hα.2 y
      exact ⟨z, rfl⟩
  · rw [(MonoidHom.ker_eq_bot_iff (θ.comp α)).mpr (hθinj.comp hα.1)]
    exact bot_le
  · have hcomp : (θ.comp α).comp ((MulAut.conj (1 : StatedSp 2 K)⁻¹).toMonoidHom.comp
        (longBlock K 2 1)) = θ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp
          (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1))) := by
      ext A
      simp [α, γ, exceptionalSpAut_longBlock]
    rw [hcomp]
    exact hinjS
  · have hcomp : (θ.comp α).comp ((MulAut.conj (1 : StatedSp 2 K)⁻¹).toMonoidHom.comp
        (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1))) =
          (θ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp (longBlock K 2 1))).comp
            (Matrix.SpecialLinearGroup.map (n := Fin 2) Fr.toRingHom) := by
      ext A
      simp [α, γ, exceptionalSpAut_shortBlock hFr]
    rw [hcomp]
    exact hinjL.comp (specialLinearGroup_map_bijective Fr).1
  · rw [map_conj_one, ← hV, ← Subgroup.map_map, ← Subgroup.map_map,
      map_exceptionalSpAut_range_longBlock]
  · rw [map_conj_one, ← hU, ← Subgroup.map_map, ← Subgroup.map_map,
      map_exceptionalSpAut_range_shortBlock]

end CFSG.RankThree.PartOne.CTP
