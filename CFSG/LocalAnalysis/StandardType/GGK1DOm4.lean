module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDickson
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailBlock
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.CharacterTheory.Wreathed.CentralSL2.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial Matrix
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry supportedBlock fixedSpace
  fixedSpace_eq_primaryComponent fixedBlockEquiv mem_supportedBlock restrictFixed
  restrictFixed_mem_orthogonalGroup)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup commSpace mem_omegaGroup
  sub_mem_commSpace natCast_finrank_sub_finrank_inf_map relIndex_omegaGroup omegaGroup_le)
open CFSG.StandardType.OrthRestTail
open CFSG.StandardType.TableBOrth (qPlusForm nondegenerate_qPlusForm isHypCoord_qPlusForm)

private noncomputable def ggK1Do4_equiv : Fin 2 × Fin 2 ≃ (Fin 2 ⊕ Fin 2) where
  toFun rs := match rs.1, rs.2 with
    | 0, 0 => Sum.inl 0
    | 0, 1 => Sum.inl 1
    | 1, 0 => Sum.inr 1
    | 1, 1 => Sum.inr 0
  invFun s := match s with
    | Sum.inl 0 => (0, 0)
    | Sum.inl 1 => (0, 1)
    | Sum.inr 0 => (1, 1)
    | Sum.inr 1 => (1, 0)
  left_inv := by rintro ⟨a, b⟩; fin_cases a <;> fin_cases b <;> rfl
  right_inv := by rintro (a | a) <;> fin_cases a <;> rfl

private noncomputable def ggK1Do4_pos : Fin 2 × Fin 2 ↪ (Fin 2 ⊕ Fin 2) :=
  ggK1Do4_equiv.toEmbedding

private noncomputable def ggK1Do4_B {K : Type} [Field K] : HypBlock (qPlusForm K 2) where
  pos := ggK1Do4_pos
  hyp₀ := isHypCoord_qPlusForm (K := K) (0 : Fin 2)
  hyp₁ := isHypCoord_qPlusForm (K := K) (1 : Fin 2)

private noncomputable def ggK1Do4_toLinE {K : Type} [Field K] :
    GL (Fin 2 ⊕ Fin 2) K ≃* ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) :=
  (Matrix.GeneralLinearGroup.toLin).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 2 ⊕ Fin 2 → K))

private theorem ggK1Do4_toLinE_apply {K : Type} [Field K] (m : GL (Fin 2 ⊕ Fin 2) K)
    (v : Fin 2 ⊕ Fin 2 → K) :
    (ggK1Do4_toLinE m : _ → _) v = (m : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v := by
  simp [ggK1Do4_toLinE, Matrix.GeneralLinearGroup.coe_toLin]

private def ggK1Do4_Ucol {K : Type} [Field K] : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
  LinearMap.ker (LinearMap.proj (Sum.inl 1)) ⊓ LinearMap.ker (LinearMap.proj (Sum.inr 0))

private def ggK1Do4_Urow {K : Type} [Field K] : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
  LinearMap.ker (LinearMap.proj (Sum.inr 0)) ⊓ LinearMap.ker (LinearMap.proj (Sum.inr 1))

private theorem ggK1Do4_mem_Ucol {K : Type} [Field K] {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ ggK1Do4_Ucol ↔ v (Sum.inl 1) = 0 ∧ v (Sum.inr 0) = 0 := by
  simp [ggK1Do4_Ucol, LinearMap.mem_ker]

private theorem ggK1Do4_mem_Urow {K : Type} [Field K] {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ ggK1Do4_Urow ↔ v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 := by
  simp [ggK1Do4_Urow, LinearMap.mem_ker]

private theorem ggK1Do4_finrank_Ucol {K : Type} [Field K] : Module.finrank K (ggK1Do4_Ucol (K :=
    K)) = 2 := by
  have hker : ggK1Do4_Ucol =
      LinearMap.ker ((LinearMap.proj (Sum.inl 1) : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] K).prod
        (LinearMap.proj (Sum.inr 0))) := by
    ext v
    simp [ggK1Do4_Ucol, LinearMap.mem_ker, LinearMap.prod_apply]
  have hsurj : Function.Surjective
      ((LinearMap.proj (Sum.inl 1) : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] K).prod
        (LinearMap.proj (Sum.inr 0))) := by
    intro p
    refine ⟨Pi.single (Sum.inl 1) p.1 + Pi.single (Sum.inr 0) p.2, ?_⟩
    simp [LinearMap.prod_apply]
  rw [hker]
  have h := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.proj (Sum.inl 1) : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] K).prod
      (LinearMap.proj (Sum.inr 0)))
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_sum, Fintype.card_fin, Module.finrank_prod, Module.finrank_self] at h
  omega

private theorem ggK1Do4_finrank_Urow {K : Type} [Field K] : Module.finrank K (ggK1Do4_Urow (K :=
    K)) = 2 := by
  have hker : ggK1Do4_Urow =
      LinearMap.ker ((LinearMap.proj (Sum.inr 0) : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] K).prod
        (LinearMap.proj (Sum.inr 1))) := by
    ext v
    simp [ggK1Do4_Urow, LinearMap.mem_ker, LinearMap.prod_apply]
  have hsurj : Function.Surjective
      ((LinearMap.proj (Sum.inr 0) : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] K).prod
        (LinearMap.proj (Sum.inr 1))) := by
    intro p
    refine ⟨Pi.single (Sum.inr 0) p.1 + Pi.single (Sum.inr 1) p.2, ?_⟩
    simp [LinearMap.prod_apply]
  rw [hker]
  have h := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.proj (Sum.inr 0) : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] K).prod
      (LinearMap.proj (Sum.inr 1)))
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_sum, Fintype.card_fin, Module.finrank_prod, Module.finrank_self] at h
  omega

private theorem ggK1Do4_Qc_eq_zero_of_mem_Ucol {K : Type} [Field K] {v : Fin 2 ⊕ Fin 2 → K}
    (hv : v ∈ ggK1Do4_Ucol) : qPlusForm K 2 v = 0 := by
  rw [ggK1Do4_mem_Ucol] at hv
  rw [qPlusForm, CFSG.LieType.Universal.Spin.quadPlus_apply, Fin.sum_univ_two]
  simp [hv.1, hv.2]

private theorem ggK1Do4_Qc_eq_zero_of_mem_Urow {K : Type} [Field K] {v : Fin 2 ⊕ Fin 2 → K}
    (hv : v ∈ ggK1Do4_Urow) : qPlusForm K 2 v = 0 := by
  rw [ggK1Do4_mem_Urow] at hv
  rw [qPlusForm, CFSG.LieType.Universal.Spin.quadPlus_apply, Fin.sum_univ_two]
  simp [hv.1, hv.2]

private theorem ggK1Do4_mul_secondCol_zero {K : Type} [Field K] (A M : Matrix (Fin 2) (Fin 2) K)
    (h0 : M 0 1 = 0) (h1 : M 1 1 = 0) :
    (A * M) 0 1 = 0 ∧ (A * M) 1 1 = 0 := by
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1]

private theorem ggK1Do4_mul_secondRow_zero {K : Type} [Field K] (M B : Matrix (Fin 2) (Fin 2) K)
    (h0 : M 1 0 = 0) (h1 : M 1 1 = 0) :
    (M * B) 1 0 = 0 ∧ (M * B) 1 1 = 0 := by
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1]

private theorem ggK1Do4_blkGL_coord {K : Type} [Field K] (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (v : Fin 2 ⊕ Fin 2 → K) :
    toMat2 (K := K) (((((ggK1Do4_B.blkGL (A, 1) : GL (Fin 2 ⊕ Fin 2) K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) ∘ ⇑ggK1Do4_pos) =
      (A : Matrix (Fin 2) (Fin 2) K) * toMat2 (K := K) (v ∘ ⇑ggK1Do4_pos) := by
  have h := HypBlock.toMat2_blkGL (K := K) ggK1Do4_B (A, 1) v
  simpa [ggK1Do4_B] using h

private theorem ggK1Do4_blkGL_left_mem_Ucol {K : Type} [Field K] (A : Matrix.SpecialLinearGroup
    (Fin 2) K)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ ggK1Do4_Ucol) :
    ((ggK1Do4_B.blkGL (A, 1) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v ∈ ggK1Do4_Ucol := by
  rw [ggK1Do4_mem_Ucol] at hv ⊢
  have hM0 : toMat2 (K := K) (fun rs => v (ggK1Do4_pos rs)) 0 1 = 0 := by
    change v (Sum.inl 1) = 0; exact hv.1
  have hM1 : toMat2 (K := K) (fun rs => v (ggK1Do4_pos rs)) 1 1 = 0 := by
    change v (Sum.inr 0) = 0; exact hv.2
  obtain ⟨h0, h1⟩ := ggK1Do4_mul_secondCol_zero (A : Matrix (Fin 2) (Fin 2) K)
    (toMat2 (K := K) (fun rs => v (ggK1Do4_pos rs))) hM0 hM1
  have key := ggK1Do4_blkGL_coord A v
  constructor
  · change toMat2 (K := K) (((((ggK1Do4_B.blkGL (A, 1) : GL (Fin 2 ⊕ Fin 2) K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) ∘ ⇑ggK1Do4_pos) 0 1 = 0
    rw [key]
    exact h0
  · change toMat2 (K := K) (((((ggK1Do4_B.blkGL (A, 1) : GL (Fin 2 ⊕ Fin 2) K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) ∘ ⇑ggK1Do4_pos) 1 1 = 0
    rw [key]
    exact h1

private theorem ggK1Do4_left_mem_omega {K : Type} [Field K] [CharP K 2] (A :
    Matrix.SpecialLinearGroup (Fin 2) K) :
    ggK1Do4_toLinE (ggK1Do4_B.blkGL (A, 1)) ∈
      omegaGroup (qPlusForm K 2) (nondegenerate_qPlusForm 2) := by
  rw [mem_omegaGroup]
  have hgO : ggK1Do4_toLinE (ggK1Do4_B.blkGL (A, 1)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (qPlusForm K 2) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [ggK1Do4_toLinE_apply]
    exact HypBlock.map_blkGL ggK1Do4_B (A, 1) v
  refine ⟨hgO, ?_⟩
  set g := ggK1Do4_toLinE (ggK1Do4_B.blkGL (A, 1)) with hg
  have hU : ∀ x ∈ ggK1Do4_Ucol, qPlusForm K 2 x = 0 :=
    fun x hx => ggK1Do4_Qc_eq_zero_of_mem_Ucol hx
  have hdim : 2 * Module.finrank K (ggK1Do4_Ucol (K := K)) =
      Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [ggK1Do4_finrank_Ucol, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_fin]
  have hle : ggK1Do4_Ucol.map (g : _ →ₗ[K] _) ≤ ggK1Do4_Ucol := by
    intro y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hgx : (g : (Fin 2 ⊕ Fin 2 → K) → (Fin 2 ⊕ Fin 2 → K)) x =
        ((ggK1Do4_B.blkGL (A, 1) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x := by
      rw [hg]; exact ggK1Do4_toLinE_apply (ggK1Do4_B.blkGL (A, 1)) x
    change (g : (Fin 2 ⊕ Fin 2 → K) → (Fin 2 ⊕ Fin 2 → K)) x ∈ ggK1Do4_Ucol
    rw [hgx]
    exact ggK1Do4_blkGL_left_mem_Ucol A hx
  have heq : ggK1Do4_Ucol.map (g : _ →ₗ[K] _) = ggK1Do4_Ucol :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [LinearEquiv.finrank_map_eq])
  have hmain := natCast_finrank_sub_finrank_inf_map
    (nondegenerate_qPlusForm 2) hU hdim hgO
  rw [inf_eq_left.mpr heq.ge, Nat.sub_self, Nat.cast_zero] at hmain
  exact ZMod.natCast_eq_zero_iff_even.mp hmain.symm

private theorem ggK1Do4_blkGL_coord_right {K : Type} [Field K] (B : Matrix.SpecialLinearGroup (Fin
    2) K)
    (v : Fin 2 ⊕ Fin 2 → K) :
    toMat2 (K := K) (((((ggK1Do4_B.blkGL (1, B) : GL (Fin 2 ⊕ Fin 2) K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) ∘ ⇑ggK1Do4_pos) =
      toMat2 (K := K) (v ∘ ⇑ggK1Do4_pos) * (B : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  have h := HypBlock.toMat2_blkGL (K := K) ggK1Do4_B (1, B) v
  simpa [ggK1Do4_B] using h

private theorem ggK1Do4_blkGL_right_mem_Urow {K : Type} [Field K] (B : Matrix.SpecialLinearGroup
    (Fin 2) K)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ ggK1Do4_Urow) :
    ((ggK1Do4_B.blkGL (1, B) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v ∈ ggK1Do4_Urow := by
  rw [ggK1Do4_mem_Urow] at hv ⊢
  have hM0 : toMat2 (K := K) (fun rs => v (ggK1Do4_pos rs)) 1 0 = 0 := by
    change v (Sum.inr 1) = 0; exact hv.2
  have hM1 : toMat2 (K := K) (fun rs => v (ggK1Do4_pos rs)) 1 1 = 0 := by
    change v (Sum.inr 0) = 0; exact hv.1
  obtain ⟨h0, h1⟩ := ggK1Do4_mul_secondRow_zero
    (toMat2 (K := K) (fun rs => v (ggK1Do4_pos rs))) (B : Matrix (Fin 2) (Fin 2) K)ᵀ hM0 hM1
  have key := ggK1Do4_blkGL_coord_right B v
  constructor
  · change toMat2 (K := K) (((((ggK1Do4_B.blkGL (1, B) : GL (Fin 2 ⊕ Fin 2) K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) ∘ ⇑ggK1Do4_pos) 1 1 = 0
    rw [key]
    exact h1
  · change toMat2 (K := K) (((((ggK1Do4_B.blkGL (1, B) : GL (Fin 2 ⊕ Fin 2) K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) ∘ ⇑ggK1Do4_pos) 1 0 = 0
    rw [key]
    exact h0

private theorem ggK1Do4_right_mem_omega {K : Type} [Field K] [CharP K 2] (B :
    Matrix.SpecialLinearGroup (Fin 2) K) :
    ggK1Do4_toLinE (ggK1Do4_B.blkGL (1, B)) ∈
      omegaGroup (qPlusForm K 2) (nondegenerate_qPlusForm 2) := by
  rw [mem_omegaGroup]
  have hgO : ggK1Do4_toLinE (ggK1Do4_B.blkGL (1, B)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (qPlusForm K 2) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [ggK1Do4_toLinE_apply]
    exact HypBlock.map_blkGL ggK1Do4_B (1, B) v
  refine ⟨hgO, ?_⟩
  set g := ggK1Do4_toLinE (ggK1Do4_B.blkGL (1, B)) with hg
  have hU : ∀ x ∈ ggK1Do4_Urow, qPlusForm K 2 x = 0 :=
    fun x hx => ggK1Do4_Qc_eq_zero_of_mem_Urow hx
  have hdim : 2 * Module.finrank K (ggK1Do4_Urow (K := K)) =
      Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [ggK1Do4_finrank_Urow, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_fin]
  have hle : ggK1Do4_Urow.map (g : _ →ₗ[K] _) ≤ ggK1Do4_Urow := by
    intro y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hgx : (g : (Fin 2 ⊕ Fin 2 → K) → (Fin 2 ⊕ Fin 2 → K)) x =
        ((ggK1Do4_B.blkGL (1, B) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x := by
      rw [hg]; exact ggK1Do4_toLinE_apply (ggK1Do4_B.blkGL (1, B)) x
    change (g : (Fin 2 ⊕ Fin 2 → K) → (Fin 2 ⊕ Fin 2 → K)) x ∈ ggK1Do4_Urow
    rw [hgx]
    exact ggK1Do4_blkGL_right_mem_Urow B hx
  have heq : ggK1Do4_Urow.map (g : _ →ₗ[K] _) = ggK1Do4_Urow :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [LinearEquiv.finrank_map_eq])
  have hmain := natCast_finrank_sub_finrank_inf_map
    (nondegenerate_qPlusForm 2) hU hdim hgO
  rw [inf_eq_left.mpr heq.ge, Nat.sub_self, Nat.cast_zero] at hmain
  exact ZMod.natCast_eq_zero_iff_even.mp hmain.symm

private noncomputable def ggK1Do4_leftHom {K : Type} [Field K] :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2 ⊕ Fin 2) K :=
  (ggK1Do4_B.blkGL).comp (MonoidHom.inl _ _)

private noncomputable def ggK1Do4_rightHom {K : Type} [Field K] :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2 ⊕ Fin 2) K :=
  (ggK1Do4_B.blkGL).comp (MonoidHom.inr _ _)

private noncomputable def ggK1Do4_T1 {K : Type} [Field K] :
    Subgroup ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) :=
  (ggK1Do4_leftHom (K := K)).range.map ggK1Do4_toLinE.toMonoidHom

private noncomputable def ggK1Do4_T2 {K : Type} [Field K] :
    Subgroup ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) :=
  (ggK1Do4_rightHom (K := K)).range.map ggK1Do4_toLinE.toMonoidHom

private noncomputable def ggK1Do4_T {K : Type} [Field K] :
    Subgroup ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) :=
  (ggK1Do4_B.blkGL.range).map ggK1Do4_toLinE.toMonoidHom

private theorem ggK1Do4_range_left_sup_right {K : Type} [Field K] :
    (ggK1Do4_leftHom (K := K)).range ⊔ (ggK1Do4_rightHom (K := K)).range =
      ggK1Do4_B.blkGL.range := by
  have htop : (MonoidHom.inl (Matrix.SpecialLinearGroup (Fin 2) K)
        (Matrix.SpecialLinearGroup (Fin 2) K)).range ⊔
      (MonoidHom.inr (Matrix.SpecialLinearGroup (Fin 2) K)
        (Matrix.SpecialLinearGroup (Fin 2) K)).range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have h : (MonoidHom.inl (Matrix.SpecialLinearGroup (Fin 2) K)
          (Matrix.SpecialLinearGroup (Fin 2) K) a) *
        (MonoidHom.inr (Matrix.SpecialLinearGroup (Fin 2) K)
          (Matrix.SpecialLinearGroup (Fin 2) K) b) = (a, b) := by
      ext <;> simp
    rw [← h]
    exact mul_mem (Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨a, rfl⟩))
      (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨b, rfl⟩))
  rw [ggK1Do4_leftHom, ggK1Do4_rightHom, MonoidHom.range_comp, MonoidHom.range_comp,
    ← Subgroup.map_sup, htop, Subgroup.map_top, MonoidHom.range_eq_map]

private theorem ggK1Do4_T1_sup_T2 {K : Type} [Field K] :
    ggK1Do4_T1 (K := K) ⊔ ggK1Do4_T2 (K := K) = ggK1Do4_T (K := K) := by
  rw [ggK1Do4_T1, ggK1Do4_T2, ggK1Do4_T, ← Subgroup.map_sup,
    ggK1Do4_range_left_sup_right]

private theorem ggK1Do4_T_le_omega {K : Type} [Field K] [CharP K 2] :
    ggK1Do4_T (K := K) ≤ omegaGroup (qPlusForm K 2) (nondegenerate_qPlusForm 2) := by
  intro x hx
  rw [ggK1Do4_T, Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [MonoidHom.mem_range] at hy
  obtain ⟨AB, rfl⟩ := hy
  rw [show AB = (AB.1, 1) * (1, AB.2) by ext <;> simp]
  rw [map_mul, map_mul]
  exact mul_mem (ggK1Do4_left_mem_omega AB.1) (ggK1Do4_right_mem_omega AB.2)

private theorem ggK1Do4_leftHom_injective {K : Type} [Field K] [CharP K 2] : Function.Injective
    (ggK1Do4_leftHom (K := K)) := by
  intro A B h
  exact congrArg Prod.fst (HypBlock.blkGL_injective ggK1Do4_B h)

private theorem ggK1Do4_rightHom_injective {K : Type} [Field K] [CharP K 2] : Function.Injective
    (ggK1Do4_rightHom (K := K)) := by
  intro A B h
  exact congrArg Prod.snd (HypBlock.blkGL_injective ggK1Do4_B h)

private theorem ggK1Do4_card_T {K : Type} [Field K] [CharP K 2] :
    Nat.card (ggK1Do4_T (K := K)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) := by
  have h1 : Nat.card (ggK1Do4_T (K := K)) =
      Nat.card ↥((ggK1Do4_B (K := K)).blkGL.range) := by
    rw [ggK1Do4_T]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective
      (ggK1Do4_B (K := K)).blkGL.range ggK1Do4_toLinE.toMonoidHom
      ggK1Do4_toLinE.injective).toEquiv).symm
  rw [h1]
  have h2 : Nat.card ↥((ggK1Do4_B (K := K)).blkGL.range) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :=
    (Nat.card_congr (MonoidHom.ofInjective (f := (ggK1Do4_B (K := K)).blkGL)
      (HypBlock.blkGL_injective (ggK1Do4_B (K := K)))).toEquiv).symm
  exact h2

private theorem ggK1Do4_card_SL2_prod {K : Type} [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) =
      (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 := by
  rw [Nat.card_prod, CFSG.Wreathed.CentralSL2.card_SL_two K]
  ring

private theorem ggK1Do4_card_omega {K : Type} [Field K] [Finite K] [CharP K 2] :
    Nat.card (omegaGroup (qPlusForm K 2) (nondegenerate_qPlusForm 2)) =
      (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 := by
  have hQ := nondegenerate_qPlusForm (K := K) 2
  have hrel : (omegaGroup (qPlusForm K 2) hQ).relIndex
      (TauCeti.QuadraticMap.orthogonalGroup (qPlusForm K 2)) = 2 :=
    relIndex_omegaGroup (qPlusForm K 2) hQ
  have hmul := Subgroup.relIndex_mul_card (omegaGroup (qPlusForm K 2) hQ)
    (TauCeti.QuadraticMap.orthogonalGroup (qPlusForm K 2))
  rw [inf_eq_left.mpr (omegaGroup_le (qPlusForm K 2) hQ), hrel] at hmul
  have hOZ : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (qPlusForm K 2)) : ℤ) =
      ((2 * (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 : ℕ) : ℤ) := by
    have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := K) hQ (m := 1)
      (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin])
      (ε := 1) (Or.inl ⟨rfl, CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K 2⟩)
    rw [h]
    simp only [Finset.Icc_self, Finset.prod_singleton]
    have hq2 : 1 ≤ Nat.card K ^ 2 := by
      rw [sq]
      exact one_le_mul (Finite.one_lt_card (α := K)).le (Finite.one_lt_card (α := K)).le
    push_cast [Nat.cast_sub hq2]
    ring
  have hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (qPlusForm K 2)) =
      2 * (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 := by
    exact_mod_cast hOZ
  have h2 : Nat.card (omegaGroup (qPlusForm K 2) (nondegenerate_qPlusForm 2)) * 2 =
      (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 * 2 := by
    rw [mul_comm (Nat.card _) 2, hmul, hO, mul_comm 2]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2

private theorem ggK1Do4_T_eq_omega {K : Type} [Field K] [Finite K] [CharP K 2] :
    ggK1Do4_T (K := K) = omegaGroup (qPlusForm K 2) (nondegenerate_qPlusForm 2) := by
  haveI : Finite (Fin 2 ⊕ Fin 2 → K) := inferInstance
  haveI : Finite ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) :=
    Finite.of_injective (fun e : _ ≃ₗ[K] _ => (e : _ → _))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite ↥(omegaGroup (qPlusForm K 2) (nondegenerate_qPlusForm 2)) := inferInstance
  refine Subgroup.eq_of_le_of_card_ge ggK1Do4_T_le_omega ?_
  rw [ggK1Do4_card_T, ggK1Do4_card_SL2_prod, ggK1Do4_card_omega]

private theorem ggK1Do4_T1_equiv {K : Type} [Field K] [CharP K 2] :
    Nonempty (ggK1Do4_T1 (K := K) ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  rw [ggK1Do4_T1]
  exact ⟨(Subgroup.equivMapOfInjective (ggK1Do4_leftHom (K := K)).range
      ggK1Do4_toLinE.toMonoidHom ggK1Do4_toLinE.injective).symm.trans
    (MonoidHom.ofInjective (f := ggK1Do4_leftHom (K := K))
      (ggK1Do4_leftHom_injective (K := K))).symm⟩

private theorem ggK1Do4_T2_equiv {K : Type} [Field K] [CharP K 2] :
    Nonempty (ggK1Do4_T2 (K := K) ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  rw [ggK1Do4_T2]
  exact ⟨(Subgroup.equivMapOfInjective (ggK1Do4_rightHom (K := K)).range
      ggK1Do4_toLinE.toMonoidHom ggK1Do4_toLinE.injective).symm.trans
    (MonoidHom.ofInjective (f := ggK1Do4_rightHom (K := K))
      (ggK1Do4_rightHom_injective (K := K))).symm⟩

private theorem ggK1Do4_blkGL_commute {K : Type} [Field K] (A B : Matrix.SpecialLinearGroup (Fin 2)
    K) :
    ggK1Do4_B.blkGL (A, 1) * ggK1Do4_B.blkGL (1, B) =
      ggK1Do4_B.blkGL (1, B) * ggK1Do4_B.blkGL (A, 1) := by
  rw [← map_mul, ← map_mul]
  congr 1
  ext <;> simp

private theorem ggK1Do4_commute {K : Type} [Field K] :
    ∀ a ∈ ggK1Do4_T1 (K := K), ∀ b ∈ ggK1Do4_T2 (K := K), a * b = b * a := by
  intro a ha b hb
  rw [ggK1Do4_T1, Subgroup.mem_map] at ha
  obtain ⟨a', ha', rfl⟩ := ha
  rw [MonoidHom.mem_range] at ha'
  obtain ⟨A, rfl⟩ := ha'
  rw [ggK1Do4_T2, Subgroup.mem_map] at hb
  obtain ⟨b', hb', rfl⟩ := hb
  rw [MonoidHom.mem_range] at hb'
  obtain ⟨B, rfl⟩ := hb'
  rw [← map_mul, ← map_mul]
  exact congrArg ggK1Do4_toLinE (ggK1Do4_blkGL_commute A B)

private theorem ggK1Do4_disjoint {K : Type} [Field K] [CharP K 2] : Disjoint (ggK1Do4_T1 (K := K))
    (ggK1Do4_T2 (K := K)) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [ggK1Do4_T1, Subgroup.mem_map] at hx1
  obtain ⟨a, ha, rfl⟩ := hx1
  rw [MonoidHom.mem_range] at ha
  obtain ⟨A, rfl⟩ := ha
  rw [ggK1Do4_T2, Subgroup.mem_map] at hx2
  obtain ⟨b, hb, hb2⟩ := hx2
  rw [MonoidHom.mem_range] at hb
  obtain ⟨B, rfl⟩ := hb
  have hAB : (A, 1) = (1, B) :=
    HypBlock.blkGL_injective ggK1Do4_B (ggK1Do4_toLinE.injective hb2.symm)
  have hA : A = 1 := congrArg Prod.fst hAB
  rw [hA, map_one, map_one]
  exact Subgroup.mem_bot.mpr rfl

private noncomputable def ggK1Do4_conjHom {K : Type} [Field K] {W W' : Type} [AddCommGroup W]
    [Module K W]
    [AddCommGroup W'] [Module K W'] (φ : W ≃ₗ[K] W') :
    (W ≃ₗ[K] W) ≃* (W' ≃ₗ[K] W') where
  toFun g := φ.symm.trans (g.trans φ)
  invFun h := φ.trans (h.trans φ.symm)
  left_inv g := by ext x; simp [LinearEquiv.trans_apply]
  right_inv h := by ext x; simp [LinearEquiv.trans_apply]
  map_mul' g h := by ext x; simp [LinearEquiv.trans_apply, LinearEquiv.mul_apply]

private theorem ggK1Do4_conjHom_apply {K : Type} [Field K] {W W' : Type} [AddCommGroup W] [Module K
    W]
    [AddCommGroup W'] [Module K W'] (φ : W ≃ₗ[K] W') (g : W ≃ₗ[K] W) (w' : W') :
    ggK1Do4_conjHom φ g w' = φ (g (φ.symm w')) := by
  simp [ggK1Do4_conjHom, LinearEquiv.trans_apply]

private theorem ggK1Do4_finrank_commSpace_conjHom {K : Type} [Field K] {W W' : Type} [AddCommGroup
    W] [Module K W]
    [AddCommGroup W'] [Module K W'] (φ : W ≃ₗ[K] W') (g : W ≃ₗ[K] W) :
    Module.finrank K (commSpace (ggK1Do4_conjHom φ g)) = Module.finrank K (commSpace g) := by
  have h : commSpace (ggK1Do4_conjHom φ g) = (commSpace g).map φ.toLinearMap := by
    ext y
    rw [Submodule.mem_map]
    constructor
    · intro hy
      rw [commSpace, LinearMap.mem_range] at hy
      obtain ⟨w', hw'⟩ := hy
      refine ⟨(g : W →ₗ[K] W) (φ.symm w') - φ.symm w',
        sub_mem_commSpace g (φ.symm w'), ?_⟩
      rw [← hw']
      simp [ggK1Do4_conjHom_apply, map_sub]
    · intro hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [commSpace, LinearMap.mem_range] at hz ⊢
      obtain ⟨v, hv⟩ := hz
      refine ⟨φ v, ?_⟩
      rw [← hv]
      simp [ggK1Do4_conjHom_apply, map_sub]
  rw [h, LinearEquiv.finrank_map_eq]

private theorem ggK1Do4_conj_mem_omega_iff {K : Type} [Field K] [CharP K 2] {W W' : Type}
    [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] [AddCommGroup W'] [Module K W'] [FiniteDimensional K W']
    {Q : QuadraticForm K W} {Q' : QuadraticForm K W'} (hQ : Q.polarBilin.Nondegenerate)
    (hQ' : Q'.polarBilin.Nondegenerate) (φ : W ≃ₗ[K] W') (hφ : ∀ w, Q' (φ w) = Q w)
    (g : W ≃ₗ[K] W) :
    ggK1Do4_conjHom φ g ∈ omegaGroup Q' hQ' ↔ g ∈ omegaGroup Q hQ := by
  have hO : ggK1Do4_conjHom φ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q' ↔
      g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    constructor
    · intro h w
      have := h (φ w)
      rw [ggK1Do4_conjHom_apply, LinearEquiv.symm_apply_apply] at this
      rwa [hφ w, hφ (g w)] at this
    · intro h w'
      have := h (φ.symm w')
      rw [ggK1Do4_conjHom_apply, hφ (g (φ.symm w'))]
      have hw : Q' w' = Q (φ.symm w') := by
        rw [← hφ (φ.symm w'), LinearEquiv.apply_symm_apply]
      rw [hw]
      exact this
  have hev : Even (Module.finrank K (commSpace (ggK1Do4_conjHom φ g))) ↔
      Even (Module.finrank K (commSpace g)) := by
    rw [ggK1Do4_finrank_commSpace_conjHom]
  rw [mem_omegaGroup, mem_omegaGroup]
  constructor
  · rintro ⟨hgO, hge⟩
    exact ⟨hO.mp hgO, hev.mp hge⟩
  · rintro ⟨hgO, hge⟩
    exact ⟨hO.mpr hgO, hev.mpr hge⟩

private theorem ggK1Do4_map_omega_symm {K : Type} [Field K] [CharP K 2] {W W' : Type} [AddCommGroup
    W] [Module K W]
    [FiniteDimensional K W] [AddCommGroup W'] [Module K W'] [FiniteDimensional K W']
    {Q : QuadraticForm K W} {Q' : QuadraticForm K W'} (hQ : Q.polarBilin.Nondegenerate)
    (hQ' : Q'.polarBilin.Nondegenerate) (φ : W ≃ₗ[K] W') (hφ : ∀ w, Q' (φ w) = Q w) :
    (omegaGroup Q' hQ').map (ggK1Do4_conjHom φ).symm.toMonoidHom = omegaGroup Q hQ := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (ggK1Do4_conj_mem_omega_iff hQ hQ' φ hφ _).mp (by simpa using hy)
  · intro hx
    refine ⟨ggK1Do4_conjHom φ x, ?_, (ggK1Do4_conjHom φ).symm_apply_apply x⟩
    exact (ggK1Do4_conj_mem_omega_iff hQ hQ' φ hφ x).mpr hx

private theorem ggK1Do4_coord {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ T1 T2 : Subgroup ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)),
      (∀ a ∈ T1, ∀ b ∈ T2, a * b = b * a) ∧ Disjoint T1 T2 ∧
      T1 ⊔ T2 = omegaGroup (qPlusForm K 2) (nondegenerate_qPlusForm 2) ∧
      Nonempty (T1 ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧
      Nonempty (T2 ≃* Matrix.SpecialLinearGroup (Fin 2) K) :=
  ⟨ggK1Do4_T1 (K := K), ggK1Do4_T2 (K := K), ggK1Do4_commute, ggK1Do4_disjoint,
    by rw [ggK1Do4_T1_sup_T2]; exact ggK1Do4_T_eq_omega,
    ggK1Do4_T1_equiv, ggK1Do4_T2_equiv⟩

theorem ggK1D_omega4_abstract {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {Q : QuadraticForm K W}
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ S₁ S₂ : Subgroup (W ≃ₗ[K] W),
      (∀ a ∈ S₁, ∀ b ∈ S₂, a * b = b * a) ∧ Disjoint S₁ S₂ ∧
      S₁ ⊔ S₂ = CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ ∧
      Nonempty (S₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧
      Nonempty (S₂ ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_isPlusType_iff hQ
    (nondegenerate_qPlusForm (K := K) 2) (n := 2)
    (by omega)
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin])
    ⟨fun _ => CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K 2, fun _ => hplus⟩
  let φ : W ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K) := e.toLinearEquiv
  obtain ⟨T1, T2, hcomm, hdisj, hjoin, hT1, hT2⟩ := ggK1Do4_coord (K := K)
  refine ⟨T1.map (ggK1Do4_conjHom φ).symm.toMonoidHom,
    T2.map (ggK1Do4_conjHom φ).symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    rw [Subgroup.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [← map_mul, ← map_mul, hcomm a' ha' b' hb']
  · rw [disjoint_iff_inf_le]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Subgroup.mem_map] at hx1 hx2
    obtain ⟨a, ha, rfl⟩ := hx1
    obtain ⟨b, hb, hb2⟩ := hx2
    have hab : b = a := (ggK1Do4_conjHom φ).symm.injective hb2
    rw [hab] at hb
    have ha1 : a = 1 := Subgroup.mem_bot.mp (hdisj.le_bot ⟨ha, hb⟩)
    rw [ha1, map_one]
    exact Subgroup.mem_bot.mpr rfl
  · rw [← Subgroup.map_sup, hjoin,
      ggK1Do4_map_omega_symm hQ (nondegenerate_qPlusForm (K := K) 2) φ e.map_app]
  · exact ⟨(Subgroup.equivMapOfInjective T1 (ggK1Do4_conjHom φ).symm.toMonoidHom
      (ggK1Do4_conjHom φ).symm.injective).symm.trans hT1.some⟩
  · exact ⟨(Subgroup.equivMapOfInjective T2 (ggK1Do4_conjHom φ).symm.toMonoidHom
      (ggK1Do4_conjHom φ).symm.injective).symm.trans hT2.some⟩

private theorem ggK1Do4_block_mem_omega_iff {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hQ : Q.polarBilin.Nondegenerate)
    {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x (X - 1)) :
    restrictFixed Q x ⟨g, hg⟩ ∈
        omegaGroup (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate ↔
      g ∈ omegaGroup Q hQ := by
  have hfin : Module.finrank K (commSpace (restrictFixed Q x ⟨g, hg⟩)) =
      Module.finrank K (commSpace g) :=
    (OddOrderIsometry.finrank_commSpace_eq_restrictFixed hx hg).symm
  have hOg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).1
  have hOe : restrictFixed Q x ⟨g, hg⟩ ∈
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) :=
    restrictFixed_mem_orthogonalGroup ⟨g, hg⟩
  rw [mem_omegaGroup, mem_omegaGroup]
  exact ⟨fun h => ⟨hOg, hfin ▸ h.2⟩, fun h => ⟨hOe, hfin.symm ▸ h.2⟩⟩

theorem ggK1D_omega4_block {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hW : Module.finrank K (primaryComponent x.toLinearMap (X - 1)) = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.restrict (primaryComponent x.toLinearMap (X - 1)))) :
    ∃ S₁ S₂ : Subgroup (V ≃ₗ[K] V),
      (∀ a ∈ S₁, ∀ b ∈ S₂, a * b = b * a) ∧ Disjoint S₁ S₂ ∧
      S₁ ⊔ S₂ = supportedBlock Q x (X - 1) ⊓
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      Nonempty (S₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧
      Nonempty (S₂ ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  set W := primaryComponent x.toLinearMap (X - 1) with hWdef
  have hWfix : fixedSpace x = W := by rw [hWdef, fixedSpace_eq_primaryComponent]
  have hdim : Module.finrank K (fixedSpace x) = 4 := by rw [hWfix]; exact hW
  have hplus' : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace x).subtype) := by
    rw [hWfix, show Q.comp W.subtype = Q.restrict W from rfl]
    exact hplus
  obtain ⟨S1', S2', hcomm', hdisj', hjoin', hT1', hT2'⟩ :=
    ggK1D_omega4_abstract (K := K) (W := fixedSpace x)
      hx.polarBilin_fixed_nondegenerate hdim hplus'
  let B : Subgroup (V ≃ₗ[K] V) := supportedBlock Q x (X - 1)
  let O' : Subgroup (fixedSpace x ≃ₗ[K] fixedSpace x) :=
    TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)
  let e := fixedBlockEquiv hx
  have hS1le : S1' ≤ O' :=
    (le_sup_left.trans (le_of_eq hjoin')).trans (omegaGroup_le (Q.comp (fixedSpace x).subtype)
      hx.polarBilin_fixed_nondegenerate)
  have hS2le : S2' ≤ O' :=
    (le_sup_right.trans (le_of_eq hjoin')).trans (omegaGroup_le (Q.comp (fixedSpace x).subtype)
      hx.polarBilin_fixed_nondegenerate)
  have hkey : ((omegaGroup (Q.comp (fixedSpace x).subtype)
        hx.polarBilin_fixed_nondegenerate).subgroupOf O').map e.symm.toMonoidHom =
      (omegaGroup Q hQ).subgroupOf B := by
    ext b
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ha' : a.val ∈ omegaGroup (Q.comp (fixedSpace x).subtype)
          hx.polarBilin_fixed_nondegenerate := Subgroup.mem_subgroupOf.mp ha
      have hrf : restrictFixed Q x ⟨(e.symm a).val, (e.symm a).2⟩ = a.val := by
        change (e (e.symm a)).val = a.val
        rw [e.apply_symm_apply a]
      exact (ggK1Do4_block_mem_omega_iff hx hQ (e.symm a).2).mp (by rwa [hrf])
    · intro hb
      refine ⟨e b, ?_, e.symm_apply_apply b⟩
      rw [Subgroup.mem_subgroupOf]
      have hb' : b.val ∈ omegaGroup Q hQ := Subgroup.mem_subgroupOf.mp hb
      have hrf : restrictFixed Q x ⟨b.val, b.2⟩ = (e b).val := rfl
      rw [← hrf]
      exact (ggK1Do4_block_mem_omega_iff hx hQ b.2).mpr hb'
  have homega_eq : omegaGroup Q hQ = CFSG.RankThree.Classical2.orthDerived Q :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT)
      (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ)
  refine ⟨((S1'.subgroupOf O').map e.symm.toMonoidHom).map B.subtype,
    ((S2'.subgroupOf O').map e.symm.toMonoidHom).map B.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    rw [Subgroup.mem_map] at ha hb
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    rw [Subgroup.mem_map] at ha₀ hb₀
    obtain ⟨a', ha', rfl⟩ := ha₀
    obtain ⟨b', hb', rfl⟩ := hb₀
    have h1 : B.subtype (e.symm.toMonoidHom a') * B.subtype (e.symm.toMonoidHom b') =
        B.subtype (e.symm.toMonoidHom (a' * b')) := by
      rw [← map_mul]
      congr 1
      rw [map_mul]
    have h2 : B.subtype (e.symm.toMonoidHom b') * B.subtype (e.symm.toMonoidHom a') =
        B.subtype (e.symm.toMonoidHom (b' * a')) := by
      rw [← map_mul]
      congr 1
      rw [map_mul]
    have hcommO : a' * b' = b' * a' := Subtype.ext
      (hcomm' a'.val (Subgroup.mem_subgroupOf.mp ha') b'.val
        (Subgroup.mem_subgroupOf.mp hb'))
    rw [h1, h2, hcommO]
  · rw [disjoint_iff_inf_le]
    intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [Subgroup.mem_map] at hz1 hz2
    obtain ⟨a₀, ha₀, rfl⟩ := hz1
    obtain ⟨b₀, hb₀, hb02⟩ := hz2
    rw [Subgroup.mem_map] at ha₀ hb₀
    obtain ⟨a', ha', rfl⟩ := ha₀
    obtain ⟨b', hb', rfl⟩ := hb₀
    have hba : b' = a' := (e.symm).injective (Subtype.ext hb02)
    rw [hba] at hb'
    have ha1 : a'.val = 1 := Subgroup.mem_bot.mp (hdisj'.le_bot ⟨
      Subgroup.mem_subgroupOf.mp ha', Subgroup.mem_subgroupOf.mp hb'⟩)
    have : a' = 1 := Subtype.ext ha1
    rw [this, map_one]
    exact Subgroup.mem_bot.mpr rfl
  · rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hS1le hS2le,
      hjoin', hkey, Subgroup.subgroupOf_map_subtype, inf_comm, homega_eq]
  · exact ⟨(Subgroup.equivMapOfInjective ((S1'.subgroupOf O').map e.symm.toMonoidHom)
        B.subtype B.subtype_injective).symm.trans
      ((Subgroup.equivMapOfInjective (S1'.subgroupOf O') e.symm.toMonoidHom
        e.symm.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hS1le).trans hT1'.some))⟩
  · exact ⟨(Subgroup.equivMapOfInjective ((S2'.subgroupOf O').map e.symm.toMonoidHom)
        B.subtype B.subtype_injective).symm.trans
      ((Subgroup.equivMapOfInjective (S2'.subgroupOf O') e.symm.toMonoidHom
        e.symm.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hS2le).trans hT2'.some))⟩

end CFSG.StandardType

end
