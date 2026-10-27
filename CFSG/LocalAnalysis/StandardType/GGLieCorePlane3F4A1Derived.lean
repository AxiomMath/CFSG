module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalA1Part1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddKernelOrbit
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

theorem ggLieF4A1_derived
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    {f : ℕ} (hf : 1 ≤ f) (hqf : D.q = 2 ^ f) (i : KernelComponent (jointChar a₁ a₂))
    (hρΨ : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i)
    (hΓ : D.Γ = D.model)
    (hmodel : GGLieSL2Model ↥(rootSpan Tag.F4 L (componentRoots (jointChar a₁ a₂) i) ⊓ D.model) f) :
    Group.IsSolvable ↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ∨
      LieModel (↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ⧸
        Subgroup.center ↥(GGLieF4PlaneRat D ρ a₁ a₂ i)) .PSL 2 2 f := by
  let S : Subgroup (ModGL Tag.F4 L) :=
    rootSpan Tag.F4 L (componentRoots (jointChar a₁ a₂) i) ⊓ D.model
  have hR : GGLieF4PlaneRat D ρ a₁ a₂ i = ⁅S, S⁆ := by
    unfold GGLieF4PlaneRat ratComp
    rw [CFSG.StandardType.F4ExplicitPos.OddKernelOrbit.ratOrbit_eq_of_image_eq hρΨ, hΓ]
  obtain ⟨K, hK_field, hK_finite, hK_card, ⟨e⟩⟩ := hmodel
  let : Field K := hK_field
  let : Finite K := hK_finite
  rcases eq_or_lt_of_le hf with rfl | hf_gt1
  · left
    have hcardK2 : Nat.card K = 2 := by simpa using hK_card
    have hsolvSL2 : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
      CFSG.StandardType.F4ExplicitPos.RationalA1.isSolvable_SL2_card_two hcardK2
    have hsolvStatedSL2 : Group.IsSolvable ↥(CFSG.Open.StatedSL 2 K) :=
      Group.isSolvable_of_surjective
        (f := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toMonoidHom)
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).surjective
    have hsolvS : Group.IsSolvable ↥S :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hcl : ⁅S, S⁆ ≤ S := Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
      simp only [commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem h₁ h₂) (S.inv_mem h₁)) (S.inv_mem h₂)
    rw [hR]
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hcl) (Subgroup.inclusion_injective hcl)
  · right
    have hf2 : 2 ≤ f := by omega
    have hcardK4 : 4 ≤ Nat.card K := by
      rw [hK_card]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    have hSL2_perfect : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hcardK4
    have hStatedSL2_perfect : Group.IsPerfect ↥(CFSG.Open.StatedSL 2 K) :=
      Group.IsPerfect.ofSurjective
        (f := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toMonoidHom)
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).surjective
    have hS_perfect : Group.IsPerfect ↥S :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hR_eq_S : GGLieF4PlaneRat D ρ a₁ a₂ i = S := by
      rw [hR]
      exact Subgroup.isPerfect_iff.mp hS_perfect
    have : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := f)
      (by rw [← Nat.card_eq_fintype_card, hK_card])
    have hZ_sl2 : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
      obtain ⟨a, ha, hmatrix⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
      have ha1 : a = 1 := by
        rcases sq_eq_one_iff.mp ha with h | h
        · exact h
        · rw [h, CharTwo.neg_eq]
      apply Subtype.ext
      rw [← hmatrix, ha1, map_one]
      rfl
    have hZ_statedSL2 : Subgroup.center (CFSG.Open.StatedSL 2 K) = ⊥ := by
      have hmap := Subgroup.map_center_eq
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
      rw [hZ_sl2, Subgroup.map_bot] at hmap
      exact hmap.symm
    have hZ_S : Subgroup.center ↥S = ⊥ := by
      have hmap := Subgroup.map_center_eq e
      rw [hZ_statedSL2] at hmap
      refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
      have hxmap : e x ∈ (Subgroup.center ↥S).map e := ⟨x, hx, rfl⟩
      rw [hmap, Subgroup.mem_bot] at hxmap
      exact e.injective (by simpa using hxmap)
    have hAdm : CFSG.Open.StatedLieAdmissible .PSL 2 2 f := by
      refine ⟨Nat.prime_two, hf, by norm_num, ?_, ?_⟩
      · intro h
        have h2 : 2 ^ f = 2 := by simpa using h
        have hle : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
        norm_num at hle
        omega
      · intro h
        have h3 : 2 ^ f = 3 := by simpa using h
        have heven : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
        rw [h3] at heven
        norm_num at heven
    have hScalars_bot : (CFSG.Open.StatedScalars (Fin 2) K).subgroupOf
        (CFSG.Open.StatedSL 2 K) = ⊥ := by
      have hmap := CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 2 K
      rw [hZ_sl2, Subgroup.map_bot] at hmap
      exact hmap.symm
    have hLieModelStatedSL2 : LieModel (CFSG.Open.StatedSL 2 K) .PSL 2 2 f := by
      rw [LieModel.classical_iff (by simp [classicalTags])]
      refine ⟨hAdm, K, hK_field, hK_finite, hK_card, ?_⟩
      exact ⟨((QuotientGroup.quotientMulEquivOfEq hScalars_bot).trans
        QuotientGroup.quotientBot).symm⟩
    have hLieModelS : LieModel ↥S .PSL 2 2 f :=
      LieModel.of_mulEquiv e.symm hLieModelStatedSL2
    rw [hR_eq_S]
    exact LieModel.quotient_center hZ_S hLieModelS

end CFSG.StandardType.LieCore
