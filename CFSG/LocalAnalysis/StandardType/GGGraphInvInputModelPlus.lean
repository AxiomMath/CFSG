module

public import CFSG.LocalAnalysis.StandardType.GGGraphInvInputModelCore
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaFieldInv

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL

private theorem ggOmW6c_normalForm_of_mem {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn4 : 4 ≤ n) (α : MulAut (matrixDerived (coordinateQuadPlus n K)))
    (hα2 : α * α = 1)
    (hout : ∀ c : matrixDerived (coordinateQuadPlus n K), α ≠ MulAut.conj c)
    (hαA : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus n K)) ⊔ AutOm.plusCompl (by omega : 1 ≤ n)) :
    (∃ u : matrixDerived (coordinateQuadPlus n K), α = MulAut.conj u * AutOm.plusRefl (by omega : 1 ≤ n)) ∨
    (∃ (u : matrixDerived (coordinateQuadPlus n K)) (σ : K ≃+* K), σ * σ = 1 ∧ σ ≠ 1 ∧
      (α = MulAut.conj u * AutOm.fieldAutP n σ ∨
        α = MulAut.conj u * (AutOm.plusRefl (by omega : 1 ≤ n) * AutOm.fieldAutP n σ))) := by
  obtain ⟨ι, hι, c, hc, hαιc⟩ := Subgroup.mem_sup_of_normal_left.mp hαA
  have hc1 : c ≠ 1 := by
    intro hc_eq_one
    obtain ⟨u, hu⟩ := hι
    exact hout u (by rw [← hαιc, hc_eq_one, mul_one, ← hu])
  have hc2 : c ^ 2 = 1 := by
    have hc2_inner : c ^ 2 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus n K)) := by
      have h_eq : ι * (c * ι * c⁻¹) * c ^ 2 = 1 := by
        have h : (ι * c) * (ι * c) = 1 := by rw [hαιc, hα2]
        rw [show ι * (c * ι * c⁻¹) * c ^ 2 = (ι * c) * (ι * c) by group]
        exact h
      have hc2_eq : c ^ 2 = (c * ι * c⁻¹)⁻¹ * ι⁻¹ := by
        rw [eq_inv_of_mul_eq_one_right h_eq, mul_inv_rev]
      rw [hc2_eq]
      exact mul_mem (inv_mem ((inferInstance :
        (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (matrixDerived (coordinateQuadPlus n K))).Normal).conj_mem ι hι c))
        (inv_mem hι)
    have hc2_plus : c ^ 2 ∈ AutOm.plusCompl (by omega : 1 ≤ n) := pow_mem hc 2
    have hmem : c ^ 2 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus n K)) ⊓ AutOm.plusCompl (by omega : 1 ≤ n) :=
      ⟨hc2_inner, hc2_plus⟩
    rw [AutOm.inner_inf_plusCompl (by omega : 3 ≤ n)] at hmem
    exact Subgroup.mem_bot.mp hmem
  rcases AutOm.involution_plusCompl (by omega : 3 ≤ n) hc hc2 hc1 with hcρ | ⟨σ, hσσ, hσ1, hcσ⟩
  · obtain ⟨u, hu⟩ := hι
    exact Or.inl ⟨u, by rw [← hαιc, hcρ, ← hu]⟩
  · obtain ⟨u, hu⟩ := hι
    exact Or.inr ⟨u, σ, hσσ, hσ1, by
      rcases hcσ with hcσ | hcσ
      · left; rw [← hαιc, hcσ, ← hu]
      · right; rw [← hαιc, hcσ, ← hu]⟩

private theorem ggOmW6cB_card_plusCompl_le_two {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn3 : 3 ≤ n) (hK : Nat.card K = 2) :
    Nat.card (AutOm.plusCompl (K := K) (by omega : 1 ≤ n)) ≤ 2 := by
  classical
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := by
    haveI : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hK
    have hsub_finset : ({0, 1} : Finset K) ⊆ Finset.univ := Finset.subset_univ _
    have hcard2 : ({0, 1} : Finset K).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [zero_ne_one]), Finset.card_singleton]
    have huniv : Finset.univ = ({0, 1} : Finset K) := by
      symm
      apply Finset.eq_of_subset_of_card_le hsub_finset
      rw [Finset.card_univ, hcard, hcard2]
    intro x
    have hx : x ∈ ({0, 1} : Finset K) := by
      rw [← huniv]
      exact Finset.mem_univ x
    simpa using hx
  have hsub : Subsingleton (K ≃+* K) := by
    constructor
    intro f g
    apply RingEquiv.ext
    intro x
    rcases h01 x with hx | hx
    · simp [hx]
    · simp [hx]
  have hρ1 : (1 : MulAut (matrixDerived (coordinateQuadPlus n K))) ≠
      AutOm.plusRefl (K := K) (by omega : 1 ≤ n) := by
    intro h
    have hmem : AutOm.plusRefl (K := K) (by omega : 1 ≤ n) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner
          (matrixDerived (coordinateQuadPlus n K)) := by
      rw [← h]
      exact Subgroup.one_mem _
    exact AutOm.plusRefl_not_mem_inner (K := K) hn3 hmem
  have hmem : ∀ c : AutOm.plusCompl (K := K) (by omega : 1 ≤ n),
      (c : MulAut (matrixDerived (coordinateQuadPlus n K))) = 1 ∨
      (c : MulAut (matrixDerived (coordinateQuadPlus n K))) =
        AutOm.plusRefl (K := K) (by omega : 1 ≤ n) := by
    intro c
    have hc_mem : (c : MulAut (matrixDerived (coordinateQuadPlus n K))) ∈
        AutOm.plusCompl (K := K) (by omega : 1 ≤ n) := c.2
    rw [AutOm.mem_plusCompl] at hc_mem
    obtain ⟨σ, hσ⟩ := hc_mem
    have hσ1 : σ = 1 := hsub.allEq σ 1
    rcases hσ with hσ | hσ
    · left
      rw [hσ, hσ1, map_one]
    · right
      rw [hσ, hσ1, map_one, mul_one]
  let f : AutOm.plusCompl (K := K) (by omega : 1 ≤ n) → Fin 2 := fun c =>
    if (c : MulAut (matrixDerived (coordinateQuadPlus n K))) =
        AutOm.plusRefl (K := K) (by omega : 1 ≤ n) then 1 else 0
  have hf : Function.Injective f := by
    intro c d hcd
    have hc := hmem c
    have hd := hmem d
    rcases hc with hc | hc <;> rcases hd with hd | hd
    · ext
      rw [hc, hd]
    · exfalso
      have h1 : f c = 0 := by simp [f, hc, hρ1]
      have h2 : f d = 1 := by simp [f, hd]
      rw [h1, h2] at hcd
      exact Fin.zero_ne_one hcd
    · exfalso
      have h1 : f c = 1 := by simp [f, hc]
      have h2 : f d = 0 := by simp [f, hd, hρ1]
      rw [h1, h2] at hcd
      exact Fin.zero_ne_one hcd.symm
    · ext
      rw [hc, hd]
  have hcard := Nat.card_le_card_of_injective f hf
  simpa using hcard

private theorem ggOmW6c_outTwoPartLeTwo_of_card_two {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn5 : 5 ≤ n) (hK : Nat.card K = 2) :
    GGOutTwoPartLeTwo (matrixDerived (coordinateQuadPlus n K)) := by
  exact ggGraphInv_outTwoPartLeTwo_of_mul (AutOm.plusCompl (K := K) (by omega : 1 ≤ n))
    (fun α => AutOm.exists_inner_mul_plusCompl hn5 α)
    (ggOmW6cB_card_plusCompl_le_two (K := K) (by omega : 3 ≤ n) hK)

private theorem ggOmW6cC_glFieldAut_eq_map {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (σ : K ≃+* K) (A : GL ι K) :
    CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut ι K σ A =
      A.map σ.toRingHom := by
  rfl

private theorem ggOmW6cC_isIsoPair_fieldPair {K : Type} [Field K] {n : ℕ} (σ : K ≃+* K) :
    CFSG.StandardType.RecipeFieldOmega.IsIsoPair (coordinateQuadPlus n K)
      (CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair (coordinateQuadPlus n K) σ
        (CFSG.SeitzReduction.E7Pilot.coordinateQuadPlus_fieldMap n σ)).val := by
  intro v
  have hSmap : coordinateSemilinearMap
      (CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair (coordinateQuadPlus n K) σ
        (CFSG.SeitzReduction.E7Pilot.coordinateQuadPlus_fieldMap n σ)).val v =
      coordinateFieldMap (2 * n) σ v := by
    funext i
    simp [CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair, coordinateSemilinearMap_apply,
      coordinateFieldMap_apply]
  rw [hSmap]
  exact CFSG.SeitzReduction.E7Pilot.coordinateQuadPlus_fieldMap n σ v

private theorem ggOmW6cC_sq_eq_one {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (hn3 : 3 ≤ n) (S : similarityPairs (coordinateQuadPlus n K))
    (hS : CFSG.StandardType.RecipeFieldOmega.IsIsoPair (coordinateQuadPlus n K) S.val)
    (α : MulAut (matrixDerived (coordinateQuadPlus n K)))
    (hconj : conjAct (coordinateQuadPlus n K) S = α) (hα2 : α * α = 1) :
    S ^ 2 = 1 := by
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadPlus n K hn3
  have hAP := coordinate_plus_point_action_properties n K hn3
  have hQne : ∃ v, (coordinateQuadPlus n K) v ≠ 0 :=
    exists_ne_zero_of_polar_nondegenerate (by omega) _ hnd
  refine CFSG.StandardType.RecipeFieldOmega.eq_one_of_conjAct_eq_one hnd hT3 hAP hQne ?_ ?_
  · rw [SubmonoidClass.coe_pow]
    exact hS.pow 2
  · rw [map_pow, hconj, pow_two, hα2]

private theorem ggOmW6cC_left_mul_map_eq_one {K : Type} [Field K] {n : ℕ}
    (S : similarityPairs (coordinateQuadPlus n K)) (σ : K ≃+* K)
    (hright : S.val.right = σ) (hS2 : S ^ 2 = 1) :
    S.val.left * S.val.left.map σ.toRingHom = 1 := by
  have h1 : S.val * S.val = 1 := by
    have h := congrArg Subtype.val hS2
    simpa [SubmonoidClass.coe_pow, pow_two] using h
  have h2 : (S.val * S.val).left = 1 := by
    have h := congrArg SemidirectProduct.left h1
    simpa using h
  rw [coordinateSemilinearGroup_mul_matrix] at h2
  rw [hright, ggOmW6cC_glFieldAut_eq_map] at h2
  exact h2

private theorem ggOmW6cC_hinv_of_mul_map_eq_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (σ : K ≃+* K) (hσσ : σ * σ = 1) (A : GL ι K)
    (hz : A * A.map σ.toRingHom = 1) :
    ∀ g : GL ι K, A * (A * g.map σ.toRingHom * A⁻¹).map σ.toRingHom * A⁻¹ = g := by
  intro g
  have hcomp : σ.toRingHom.comp σ.toRingHom = RingHom.id K := by
    ext x
    change σ (σ x) = x
    have h := congrArg (fun f : K ≃+* K => f x) hσσ
    simpa using h
  have hmap2 : (g.map σ.toRingHom).map σ.toRingHom = g := by
    have h := congrArg (fun f : GL ι K →* GL ι K => f g)
      (Matrix.GeneralLinearGroup.map_comp σ.toRingHom σ.toRingHom)
    rw [hcomp, Matrix.GeneralLinearGroup.map_id] at h
    simpa using h.symm
  have h1 : (A * g.map σ.toRingHom * A⁻¹).map σ.toRingHom =
      A.map σ.toRingHom * g * (A.map σ.toRingHom)⁻¹ := by
    simp only [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_inv, hmap2]
  rw [h1]
  calc A * (A.map σ.toRingHom * g * (A.map σ.toRingHom)⁻¹) * A⁻¹
      = (A * A.map σ.toRingHom) * g * (A * A.map σ.toRingHom)⁻¹ := by group
    _ = g := by rw [hz]; group

private theorem ggOmW6cC_isometry_fieldMap {K : Type} [Field K] {n : ℕ} (σ : K ≃+* K)
    (A : GL (Fin (2 * n)) K) (hA : A ∈ matrixIsometries (coordinateQuadPlus n K)) :
    ∀ v : Fin (2 * n) → K,
      coordinateQuadPlus n K (Matrix.mulVec A.val (fun i => σ (v i))) =
        σ (coordinateQuadPlus n K v) := by
  intro v
  have h1 := map_mulVec_of_mem (Q := coordinateQuadPlus n K) hA (fun i => σ (v i))
  exact h1.trans (CFSG.SeitzReduction.E7Pilot.coordinateQuadPlus_fieldMap n σ v)

private theorem ggOmW6cC_conjAct_apply_val {K : Type} [Field K] {n : ℕ}
    (S : similarityPairs (coordinateQuadPlus n K)) (σ : K ≃+* K) (hright : S.val.right = σ)
    (g : matrixDerived (coordinateQuadPlus n K)) :
    ((conjAct (coordinateQuadPlus n K) S g : matrixDerived (coordinateQuadPlus n K)) :
        GL (Fin (2 * n)) K) =
      S.val.left * (g : GL (Fin (2 * n)) K).map σ.toRingHom * S.val.left⁻¹ := by
  rw [conjAct_apply, matrixDerivedConjugation_val, hright, ggOmW6cC_glFieldAut_eq_map]

private theorem ggOmW6cC_commutative_of_semilinear {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn4 : 4 ≤ n) (b : matrixDerived (coordinateQuadPlus n K))
    (hodd : Odd (orderOf b)) (α : MulAut (matrixDerived (coordinateQuadPlus n K)))
    (hα2 : α * α = 1)
    (hfix : ∀ g ∈ Subgroup.centralizer ({b} : Set (matrixDerived (coordinateQuadPlus n K))),
      α g = g)
    (σ : K ≃+* K) (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    (S : similarityPairs (coordinateQuadPlus n K))
    (hS : CFSG.StandardType.RecipeFieldOmega.IsIsoPair (coordinateQuadPlus n K) S.val)
    (hconjS : conjAct (coordinateQuadPlus n K) S = α) (hright : S.val.right = σ)
    (hAO : S.val.left ∈ matrixIsometries (coordinateQuadPlus n K)) :
    ∀ x ∈ Subgroup.centralizer ({b} : Set (matrixDerived (coordinateQuadPlus n K))),
      ∀ y ∈ Subgroup.centralizer ({b} : Set (matrixDerived (coordinateQuadPlus n K))),
        x * y = y * x := by
  intro x hx y hy
  haveI : Fintype K := Fintype.ofFinite K
  have hn3 : 3 ≤ n := by omega
  have hodd' : Odd (orderOf (b.val : GL (Fin (2 * n)) K)) := by
    simpa [Subgroup.orderOf_coe] using hodd
  have hnd : (coordinateQuadPlus n K).polarBilin.Nondegenerate :=
    (regular_coordinateQuadPlus n K hn3).1
  have hS2 : S ^ 2 = 1 := ggOmW6cC_sq_eq_one hn3 S hS α hconjS hα2
  have hz : S.val.left * S.val.left.map σ.toRingHom = 1 :=
    ggOmW6cC_left_mul_map_eq_one S σ hright hS2
  have hinv : ∀ g : GL (Fin (2 * n)) K,
      S.val.left * (S.val.left * g.map σ.toRingHom * S.val.left⁻¹).map σ.toRingHom *
        S.val.left⁻¹ = g :=
    ggOmW6cC_hinv_of_mul_map_eq_one σ hσσ S.val.left hz
  have hAΦ : ∀ v : Fin (2 * n) → K,
      coordinateQuadPlus n K (Matrix.mulVec S.val.left.val (fun i => σ (v i))) =
        σ (coordinateQuadPlus n K v) :=
    ggOmW6cC_isometry_fieldMap σ S.val.left hAO
  have hfixW4 : ∀ g ∈ Subgroup.centralizer ({b.val} : Set (GL (Fin (2 * n)) K)) ⊓
      CFSG.Open.StatedOmega ⇑(coordinateQuadPlus n K),
      S.val.left * g.map σ.toRingHom * S.val.left⁻¹ = g := by
    intro g hg
    have hgΩ : g ∈ matrixDerived (coordinateQuadPlus n K) :=
      (matrixDerived_eq_statedOmega (coordinateQuadPlus n K)).symm ▸ hg.2
    let g' : matrixDerived (coordinateQuadPlus n K) := ⟨g, hgΩ⟩
    have hgb : g' ∈ Subgroup.centralizer
        ({b} : Set (matrixDerived (coordinateQuadPlus n K))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg.1)
    have happ := hfix g' hgb
    have h1 : ((α g' : matrixDerived (coordinateQuadPlus n K)) : GL (Fin (2 * n)) K) =
        S.val.left * g.map σ.toRingHom * S.val.left⁻¹ := by
      rw [← hconjS]
      exact ggOmW6cC_conjAct_apply_val S σ hright g'
    have h2 := congrArg Subtype.val happ
    rw [h1] at h2
    simpa using h2
  have hcomm := CFSG.StandardType.ClassicalBlocks.isMulCommutative_centralizer_of_fieldInv_Omega
    σ hσ1 (coordinateQuadPlus n K) hnd (by rw [Fintype.card_fin]; omega) S.val.left hAΦ hinv
    b.val ((matrixDerived_eq_statedOmega (coordinateQuadPlus n K)).le b.2) hodd' hfixW4
  have hx' : (x : GL (Fin (2 * n)) K) ∈
      Subgroup.centralizer ({b.val} : Set (GL (Fin (2 * n)) K)) ⊓
        CFSG.Open.StatedOmega ⇑(coordinateQuadPlus n K) := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx)), ?_⟩
    exact (matrixDerived_eq_statedOmega (coordinateQuadPlus n K)).le x.2
  have hy' : (y : GL (Fin (2 * n)) K) ∈
      Subgroup.centralizer ({b.val} : Set (GL (Fin (2 * n)) K)) ⊓
        CFSG.Open.StatedOmega ⇑(coordinateQuadPlus n K) := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)), ?_⟩
    exact (matrixDerived_eq_statedOmega (coordinateQuadPlus n K)).le y.2
  apply Subtype.ext
  exact hcomm x.val hx' y.val hy'

private theorem ggOmW6c_field_centralizer_commutative {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn4 : 4 ≤ n) (b : matrixDerived (coordinateQuadPlus n K))
    (hodd : Odd (orderOf b)) (α : MulAut (matrixDerived (coordinateQuadPlus n K)))
    (hα2 : α * α = 1)
    (hfix : ∀ g ∈ Subgroup.centralizer ({b} : Set (matrixDerived (coordinateQuadPlus n K))),
      α g = g)
    (u : matrixDerived (coordinateQuadPlus n K)) (σ : K ≃+* K) (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hα : α = MulAut.conj u * AutOm.fieldAutP n σ ∨
      α = MulAut.conj u * (AutOm.plusRefl (K := K) (by omega : 1 ≤ n) * AutOm.fieldAutP n σ)) :
    ∀ x ∈ Subgroup.centralizer ({b} : Set (matrixDerived (coordinateQuadPlus n K))),
      ∀ y ∈ Subgroup.centralizer ({b} : Set (matrixDerived (coordinateQuadPlus n K))),
        x * y = y * x := by
  have hn : 1 ≤ n := by omega
  have huO : u.val ∈ matrixIsometries (coordinateQuadPlus n K) :=
    matrixDerived_le_isometries (coordinateQuadPlus n K) u.2
  have hσmap := CFSG.SeitzReduction.E7Pilot.coordinateQuadPlus_fieldMap n σ
  rcases hα with hα | hα
  · let S : similarityPairs (coordinateQuadPlus n K) :=
      matrixIsometryInclusion (coordinateQuadPlus n K) ⟨u.val, huO⟩ *
        CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair (coordinateQuadPlus n K) σ hσmap
    have hSval : S.val = SemidirectProduct.inl u.val *
        (CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair
          (coordinateQuadPlus n K) σ hσmap).val := by
      rw [show S = _ * _ from rfl, Subgroup.coe_mul, matrixIsometryInclusion_val]
    have hS : CFSG.StandardType.RecipeFieldOmega.IsIsoPair (coordinateQuadPlus n K) S.val :=
      hSval ▸ (CFSG.StandardType.RecipeFieldOmega.isIsoPair_inl huO).mul
        (ggOmW6cC_isIsoPair_fieldPair σ)
    have hright : S.val.right = σ := by
      rw [show S = _ * _ from rfl, Subgroup.coe_mul, coordinateSemilinearGroup_mul_field,
        matrixIsometryInclusion_val, SemidirectProduct.right_inl, one_mul,
        CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair_right]
    have hSleft : S.val.left = u.val := by
      rw [show S = _ * _ from rfl, Subgroup.coe_mul, coordinateSemilinearGroup_mul_matrix,
        matrixIsometryInclusion_val, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair_left]
      simp
    have hconjS : conjAct (coordinateQuadPlus n K) S = α := by
      rw [hα]
      rw [show S = matrixIsometryInclusion (coordinateQuadPlus n K) ⟨u.val, huO⟩ *
          CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair
            (coordinateQuadPlus n K) σ hσmap from rfl]
      rw [map_mul, conjAct_inclusion_of_mem _ u.2, ← AutOm.fieldAutP_apply]
    exact ggOmW6cC_commutative_of_semilinear hn4 b hodd α hα2 hfix σ hσσ hσ1 S hS hconjS
      hright (by rw [hSleft]; exact huO)
  · have hplus : AutOm.plusRefl (K := K) (by omega : 1 ≤ n) = AutOm.plusRefl (K := K) hn :=
      congrArg (AutOm.plusRefl (K := K)) (Subsingleton.elim _ _)
    rw [hplus] at hα
    let w : Fin (2 * n) → K := CFSG.SeitzReduction.OmegaPilot.plusUnitVector hn
    have hw : coordinateQuadPlus n K w ≠ 0 := AutOm.plusUnitVector_form_ne_zero hn
    have hrO : CFSG.RankThree.PartOne.AUTSL.reflMat (coordinateQuadPlus n K) w hw ∈
        matrixIsometries (coordinateQuadPlus n K) :=
      CFSG.RankThree.PartOne.AUTSL.reflMat_mem_isometries _ _
    let S : similarityPairs (coordinateQuadPlus n K) :=
      matrixIsometryInclusion (coordinateQuadPlus n K) ⟨u.val, huO⟩ *
        (matrixIsometryInclusion (coordinateQuadPlus n K)
          ⟨CFSG.RankThree.PartOne.AUTSL.reflMat (coordinateQuadPlus n K) w hw, hrO⟩ *
          CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair
            (coordinateQuadPlus n K) σ hσmap)
    have hSval : S.val = SemidirectProduct.inl u.val *
        (SemidirectProduct.inl (CFSG.RankThree.PartOne.AUTSL.reflMat
          (coordinateQuadPlus n K) w hw) *
        (CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair
          (coordinateQuadPlus n K) σ hσmap).val) := by
      rw [show S = _ * _ from rfl, Subgroup.coe_mul, Subgroup.coe_mul,
        matrixIsometryInclusion_val, matrixIsometryInclusion_val]
    have hS : CFSG.StandardType.RecipeFieldOmega.IsIsoPair (coordinateQuadPlus n K) S.val :=
      hSval ▸ (CFSG.StandardType.RecipeFieldOmega.isIsoPair_inl huO).mul
        ((CFSG.StandardType.RecipeFieldOmega.isIsoPair_inl hrO).mul
          (ggOmW6cC_isIsoPair_fieldPair σ))
    have hright : S.val.right = σ := by
      rw [show S = _ * _ from rfl, Subgroup.coe_mul, coordinateSemilinearGroup_mul_field,
        Subgroup.coe_mul, coordinateSemilinearGroup_mul_field,
        matrixIsometryInclusion_val, matrixIsometryInclusion_val,
        SemidirectProduct.right_inl, SemidirectProduct.right_inl, one_mul, one_mul,
        CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair_right]
    have hSleft : S.val.left = u.val * CFSG.RankThree.PartOne.AUTSL.reflMat
        (coordinateQuadPlus n K) w hw := by
      rw [show S = _ * _ from rfl, Subgroup.coe_mul, coordinateSemilinearGroup_mul_matrix,
        matrixIsometryInclusion_val, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        Subgroup.coe_mul, coordinateSemilinearGroup_mul_matrix, matrixIsometryInclusion_val,
        SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair_left]
      simp
    have hconjS : conjAct (coordinateQuadPlus n K) S = α := by
      rw [hα]
      rw [show S = matrixIsometryInclusion (coordinateQuadPlus n K) ⟨u.val, huO⟩ *
          (matrixIsometryInclusion (coordinateQuadPlus n K)
            ⟨CFSG.RankThree.PartOne.AUTSL.reflMat (coordinateQuadPlus n K) w hw, hrO⟩ *
          CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair
            (coordinateQuadPlus n K) σ hσmap) from rfl]
      rw [map_mul, map_mul, conjAct_inclusion_of_mem _ u.2,
        show conjAct (coordinateQuadPlus n K) (matrixIsometryInclusion (coordinateQuadPlus n K)
          ⟨CFSG.RankThree.PartOne.AUTSL.reflMat (coordinateQuadPlus n K) w hw, hrO⟩) =
          AutOm.plusRefl (K := K) hn from rfl, ← AutOm.fieldAutP_apply]
    exact ggOmW6cC_commutative_of_semilinear hn4 b hodd α hα2 hfix σ hσσ hσ1 S hS hconjS
      hright (by rw [hSleft]; exact mul_mem huO hrO)

private theorem ggOmW6c_field_false {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn4 : 4 ≤ n) (b : matrixDerived (coordinateQuadPlus n K)) (hodd : Odd (orderOf b))
    (hL : ∃ L₁ : Subgroup (matrixDerived (coordinateQuadPlus n K)),
      IsComponentOf L₁ (Subgroup.centralizer ({b} : Set (matrixDerived (coordinateQuadPlus n K)))))
    (α : MulAut (matrixDerived (coordinateQuadPlus n K))) (hα2 : α * α = 1)
    (hfix : ∀ g ∈ Subgroup.centralizer ({b} : Set (matrixDerived (coordinateQuadPlus n K))),
      α g = g)
    (u : matrixDerived (coordinateQuadPlus n K)) (σ : K ≃+* K) (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hα : α = MulAut.conj u * AutOm.fieldAutP n σ ∨
      α = MulAut.conj u * (AutOm.plusRefl (K := K) (by omega : 1 ≤ n) * AutOm.fieldAutP n σ)) :
    False := by
  obtain ⟨L, hL⟩ := hL
  have hcomm := ggOmW6c_field_centralizer_commutative hn4 b hodd α hα2 hfix u σ hσσ hσ1 hα
  haveI : IsMulCommutative
      ↥(Subgroup.centralizer ({b} : Set (matrixDerived (coordinateQuadPlus n K)))) :=
    ⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩
  exact ggGraphInv_component_false_of_solvable (inferInstance) hL

private theorem ggOmW6c_graph_clauses {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn4 : 4 ≤ n) (b : matrixDerived (coordinateQuadPlus n K)) (hodd : Odd (orderOf b))
    (α : MulAut (matrixDerived (coordinateQuadPlus n K))) (hα2 : α * α = 1) (hαb : α b = b)
    (hfix : ∀ g ∈ Subgroup.centralizer ({b} : Set (matrixDerived (coordinateQuadPlus n K))),
      α g = g)
    (u : matrixDerived (coordinateQuadPlus n K))
    (hα : α = MulAut.conj u * AutOm.plusRefl (K := K) (by omega : 1 ≤ n)) :
    Nat.card K = 2 ∧ GGGraphInvFixClauses α := by
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have h8 : 8 ≤ 2 * n := by omega
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus n K hn3
  have hw : coordinateQuadPlus n K
      (CFSG.SeitzReduction.OmegaPilot.plusUnitVector hn1) ≠ 0 :=
    AutOm.plusUnitVector_form_ne_zero (K := K) hn1
  have hRΩ : reflMat (coordinateQuadPlus n K)
      (CFSG.SeitzReduction.OmegaPilot.plusUnitVector hn1) hw ∉
      CFSG.Open.StatedOmega ⇑(coordinateQuadPlus n K) := by
    have h := reflMat_not_mem_derived (Q := coordinateQuadPlus n K) hnd hT
      (CFSG.SeitzReduction.OmegaPilot.plusUnitVector hn1) hw
    rwa [matrixDerived_eq_statedOmega] at h
  have hρ : AutOm.plusRefl (K := K) (by omega : 1 ≤ n) =
      reflAut (coordinateQuadPlus n K)
        (CFSG.SeitzReduction.OmegaPilot.plusUnitVector hn1) hw := rfl
  obtain ⟨s, hsO, hsΩ, hs2, hconj⟩ :=
    ggGraphInv_graph_lift (coordinateQuadPlus n K) hnd h8 u
      (CFSG.SeitzReduction.OmegaPilot.plusUnitVector hn1) hw hRΩ α hα2
      (by rw [hα, hρ])
  have hbΩ : (b : GL (Fin (2 * n)) K) ∈
      CFSG.Open.StatedOmega ⇑(coordinateQuadPlus n K) := by
    rw [← matrixDerived_eq_statedOmega]
    exact b.2
  have hodd' : Odd (orderOf (b : GL (Fin (2 * n)) K)) := by
    rwa [Subgroup.orderOf_coe]
  have hsb : s * (b : GL (Fin (2 * n)) K) = (b : GL (Fin (2 * n)) K) * s :=
    ggGraphInv_conjBy_commute (coordinateQuadPlus n K) α s hconj b hαb
  have hsC : ∀ g ∈ Subgroup.centralizer
      ({(b : GL (Fin (2 * n)) K)} : Set (GL (Fin (2 * n)) K)) ⊓
      CFSG.Open.StatedOmega ⇑(coordinateQuadPlus n K), s * g = g * s := by
    intro g hg
    have hgΩ : g ∈ matrixDerived (coordinateQuadPlus n K) := by
      rw [matrixDerived_eq_statedOmega]
      exact hg.2
    let g' : matrixDerived (coordinateQuadPlus n K) := ⟨g, hgΩ⟩
    have hg' : g' ∈ Subgroup.centralizer
        ({b} : Set (matrixDerived (coordinateQuadPlus n K))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      first
        | simpa using (Subgroup.mem_centralizer_singleton_iff.mp hg.1)
        | simpa using (Subgroup.mem_centralizer_singleton_iff.mp hg.1).symm
    have hcomm := ggGraphInv_conjBy_commute (coordinateQuadPlus n K) α s hconj g'
      (hfix g' hg')
    simpa [g'] using hcomm
  exact ggGraphInv_three_conclusions_of_transvection (coordinateQuadPlus n K) hnd h8
    (b : GL (Fin (2 * n)) K) hbΩ hodd' α s hsO hsΩ hs2 hsb hsC hconj

theorem ggGraphInvInputModel_plus_clauses {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn4 : 4 ≤ n) (p : ℕ) (b : matrixDerived (coordinateQuadPlus n K))
    (α : MulAut (matrixDerived (coordinateQuadPlus n K)))
    (hp : p.Prime) (hp2 : p ≠ 2) (hb : b ≠ 1) (hbp : b ^ p = 1)
    (hα2 : α * α = 1) (hout : ∀ c : matrixDerived (coordinateQuadPlus n K), α ≠ MulAut.conj c)
    (hαb : α b = b)
    (hcomp : ∃ L₁ : Subgroup (matrixDerived (coordinateQuadPlus n K)),
      IsComponentOf L₁ (Subgroup.centralizer {b}))
    (hcent : ∀ g ∈ Subgroup.centralizer {b}, α g = g)
    (hαA : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus n K)) ⊔ AutOm.plusCompl (by omega : 1 ≤ n)) :
    Nat.card K = 2 ∧ GGGraphInvFixClauses α := by
  have hodd : Odd (orderOf b) := ggGraphInv_odd_orderOf hp hp2 hb hbp
  rcases ggOmW6c_normalForm_of_mem hn4 α hα2 hout hαA with
    ⟨u, hα⟩ | ⟨u, σ, hσσ, hσ1, hαor⟩
  · exact ggOmW6c_graph_clauses hn4 b hodd α hα2 hαb hcent u hα
  · exact (ggOmW6c_field_false hn4 b hodd hcomp α hα2 hcent u σ hσσ hσ1 hαor).elim

theorem ggGraphInvInputModel_plus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn5 : 5 ≤ n) : GGGraphInvInputModel (matrixDerived (coordinateQuadPlus n K)) := by
  intro p b α hp hp2 hb1 hbp hα2 hout hαb hL hfix
  obtain ⟨ι, hι, c, hc, hαιc⟩ := AutOm.exists_inner_mul_plusCompl hn5 α
  have hαA : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (coordinateQuadPlus n K)) ⊔ AutOm.plusCompl (by omega : 1 ≤ n) := by
    rw [hαιc]
    exact Subgroup.mul_mem_sup hι hc
  obtain ⟨hK, hcl⟩ := ggGraphInvInputModel_plus_clauses (by omega) p b α hp hp2 hb1 hbp hα2 hout
    hαb hL hfix hαA
  exact ⟨ggOmW6c_outTwoPartLeTwo_of_card_two hn5 hK, hcl⟩

end CFSG.StandardType
