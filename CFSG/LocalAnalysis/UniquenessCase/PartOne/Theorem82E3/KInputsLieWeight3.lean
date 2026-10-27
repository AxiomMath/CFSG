module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLie
import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalCoords
import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalOrthLevi
import CFSG.GroupTheory.WeirSylow.UniqueE27Symplectic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordsSignedCompare
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelUnpack

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open CFSG.LinearAlgebra CFSG.ClassicalGroups.Symplectic Subgroup
open scoped MatrixGroups

private theorem weightThree_isQuasisimple_sl2 {F : Type} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) : CFSG.IsQuasisimple SL(2, F) := by
  obtain ⟨a, ha, hasq⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card F h4
  have hperf : Group.IsPerfect SL(2, F) := ⟨Matrix.SL2.commutator_eq_top ha hasq⟩
  have hsimple : IsSimpleGroup (SL(2, F) ⧸ center SL(2, F)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hc
  have hcomm : IsMulCommutative (SL(2, F) ⧸ center SL(2, F)) :=
    ⟨⟨fun x y => by_contra fun hxy => hc ⟨x, y, hxy⟩⟩⟩
  exact Group.IsPerfect.not_isMulCommutative _ hcomm

private theorem weightThree_sl2_center_eq_bot {F : Type} [Field F] [CharP F 2] :
    center SL(2, F) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
  subst hr1
  rw [Subgroup.mem_bot]
  ext i j
  have := congrFun (congrFun hrA i) j
  simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm

theorem k7Sp6Weight3_holds :
    K7Sp6Weight3 := by
  intro Y _ _ f hf h A _ _ c hc v hv
  have hq : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hZ : center Y = ⊥ := Theorem82.center_eq_bot_of_isLie811_of_ne h (by decide)
    (fun _ h2 => by rw [h2] at hq; norm_num at hq)
  obtain ⟨-, -, -, -, hm⟩ := h
  obtain ⟨K, _, _, _, hK, hK3, ⟨e⟩⟩ :=
    Theorem82.ModelUnpack.exists_model_of_lieModel_psp (by decide) hm
  have hs := isCubeRootBlock_cubeRootBlockStd
    (Theorem82.ModelUnpack.three_ne_zero_of_charP (K := K) Nat.prime_two (by decide))
  have hN : (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K) = ⊥ :=
    StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot
  obtain ⟨g, hg⟩ := (Sp6ThreeLocal.c₀_signedCoords hs).exists_conj_eq_of_model _
    (by rw [hN, Subgroup.card_bot]; norm_num)
    (GroupTheory.WeirSylow.uniqueElemSylow_statedProj_statedSp_three K hK3) (center Y)
    (by rw [hZ, Subgroup.card_bot]; norm_num) e hc
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hNi : Function.Injective
      (QuotientGroup.mk' ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN]
  have hZi : Function.Injective (QuotientGroup.mk' (center Y)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  let πH : StatedSp 3 K ≃* StatedProj (StatedSp 3 K) :=
    MulEquiv.ofBijective _ ⟨hNi, QuotientGroup.mk'_surjective _⟩
  let πY : Y ≃* Y ⧸ center Y := MulEquiv.ofBijective _ ⟨hZi, QuotientGroup.mk'_surjective _⟩
  let Θ : StatedSp 3 K ≃* Y := (πH.trans e.symm).trans πY.symm
  have hΘ : ∀ x, e (QuotientGroup.mk' (center Y) (Θ x)) = QuotientGroup.mk' _ x := fun x => by
    change e (πY (πY.symm (e.symm (πH x)))) = πH x
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have hcw : ∀ w, c w = Θ (g₀ * Sp6ThreeLocal.c₀ hs w * g₀⁻¹) := fun w => by
    apply hZi
    apply e.injective
    rw [hΘ, hg w, map_mul, map_mul, map_inv]
  obtain ⟨n, hn⟩ := hc.2.2.2 1 v hv
  have hv' : c (Multiplicative.ofAdd v) = n * c (Multiplicative.ofAdd ![1, 1, 1]) * n⁻¹ := by
    rw [hn]
    congr 2
    funext i
    fin_cases i <;> simp
  let φ : StatedSp 3 K →* Y :=
    (MulAut.conj n).toMonoidHom.comp (Θ.toMonoidHom.comp (MulAut.conj g₀).toMonoidHom)
  have hφ : Function.Injective φ :=
    (MulAut.conj n).injective.comp (Θ.injective.comp (MulAut.conj g₀).injective)
  have hcv : c (Multiplicative.ofAdd v) =
      φ (Sp6ThreeLocal.c₀ hs (Multiplicative.ofAdd ![1, 1, 1])) := by
    rw [hv', hcw]
    rfl
  let χ : SL(2, K) →* Y := φ.comp Sp6ThreeLocal.weightThreeSL
  have hχ : Function.Injective χ := hφ.comp Sp6ThreeLocal.weightThreeSL_injective
  have eK : ↥χ.range ≃* SL(2, K) := (MonoidHom.ofInjective hχ).symm
  refine ⟨χ.range, ?_, CFSG.IsQuasisimple.of_mulEquiv eK
    (weightThree_isQuasisimple_sl2 (by rw [hK]; exact hq)), ?_⟩
  · rintro _ ⟨z, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy, hcv]
    change φ _ * φ (Sp6ThreeLocal.weightThreeSL z) = φ (Sp6ThreeLocal.weightThreeSL z) * φ _
    rw [← map_mul, ← map_mul, (Sp6ThreeLocal.commute_c₀_point_111_weightThreeSL hs z).eq]
  · have hcen : Nat.card (center ↥χ.range) = 1 := by
      rw [Nat.card_congr (Subgroup.centerCongr eK).toEquiv, weightThree_sl2_center_eq_bot,
        Subgroup.card_bot]
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥χ.range)
    rw [hcen, mul_one, Nat.card_congr eK.toEquiv] at hcard
    rw [← hcard, ← hs.orderOf_eq_three]
    exact orderOf_dvd_natCard _

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
