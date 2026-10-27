module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBTvFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Two
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley TableB TableBSymp Matrix

namespace TableBF4TwoTB

section Tv


theorem sq_mem_inn_adjoint_F4_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (φ : MulAut (adjointGroup .F4 K)) :
    φ ^ 2 ∈ Set.range (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  obtain ⟨-, -, ⟨Θ, -, -, hΘker⟩, -⟩ :=
    CFSG.LieType.Chevalley.even_F4_exact_automorphism_normal_form (f := 1) le_rfl K hK'
  have hsq : ∀ y : Multiplicative (ZMod (2 * 1)), y ^ 2 = 1 := by
    have h0 : ∀ z : ZMod (2 * 1), z + z = 0 := by decide
    intro y
    rw [pow_two]
    exact congrArg Multiplicative.ofAdd (h0 (Multiplicative.toAdd y))
  have h1 : φ ^ 2 ∈ Θ.ker := MonoidHom.mem_ker.mpr ((map_pow Θ φ 2).trans (hsq _))
  rw [hΘker] at h1
  exact MonoidHom.mem_range.mp h1

theorem ggNoTransvectionSCrJ_adjoint_F4_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hS : GGF4TwoNonToralSolv K) (hN : GGF4TwoNormIsometry K) :
    GGNoTransvectionSCrJ 3 3 (adjointGroup .F4 K)
      (Set.range (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K))) := by
  classical
  have hcp : GGCenterPrime 3 (adjointGroup .F4 K) :=
    TableBExcTwoTv.ggCenterPrime_of_mulEquiv_tv (TableBF4.recipeEquiv K).symm
      (ExcSplitL.ggCenterPrime_recipe_F4 Nat.prime_three (by norm_num))
  refine ggNoTransvectionSCrJ_of_frameTorus subset_rfl
    (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := K)) hcp
    (sq_mem_inn_adjoint_F4_two hK) (tE_injective (K := K)) ?_ hN
  intro E hE hr hsc hJE
  by_contra hnc
  obtain ⟨e, heE, he1, hens⟩ := hJE
  exact hens (hS E hE hr hsc hnc e heE he1)

theorem ggNoTransvectionSCrJ_F4_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hS : GGF4TwoNonToralSolv K) (hN : GGF4TwoNormIsometry K) :
    GGNoTransvectionSCrJ 3 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  refine ggNoTransvectionSCrJ_of_mulEquiv (TableBF4.recipeEquiv K) ?_
    (ggNoTransvectionSCrJ_adjoint_F4_two hK hS hN)
  intro φ hφ
  obtain ⟨g, rfl⟩ := TableBF4.idImage_subset_inn K hφ
  refine ⟨(TableBF4.recipeEquiv K) g, ?_⟩
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply, map_mul, map_inv]

theorem largeEvenLabelAll_noTransvectionSCrJ_f4TwoThree (hS : GGF4TwoNonToralSolvInput)
    (hN : GGF4TwoNormIsometryInput) {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTableBF4TwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGNoTransvectionSCrJ p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn, rfl⟩ := h
  dsimp only at htag hn
  subst htag
  subst hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK])
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 3, TableBF4Two.ggTorusLift_F4Two,
    ggNoTransvectionSCrJ_F4_two hK2 (hS K hK2) (hN K hK2)⟩

theorem ggLTransvectionCenterInputOn_f4TwoThree_holds (hS : GGF4TwoNonToralSolvInput)
    (hN : GGF4TwoNormIsometryInput) : GGLTransvectionCenterInputOn GGTableBF4TwoLabel :=
  ggLTransvectionCenterInputOn_of_labelsSCrJ' ggLNoncyclicInput_holds fun _ _ _ _ h =>
    largeEvenLabelAll_noTransvectionSCrJ_f4TwoThree hS hN h

end Tv

end TableBF4TwoTB

end CFSG.StandardType

end
