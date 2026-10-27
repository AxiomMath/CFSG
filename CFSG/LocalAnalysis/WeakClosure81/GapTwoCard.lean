module

public import CFSG.LocalAnalysis.WeakClosure81.TvCenterAutInner
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.CGT.PushingUpLit.E3A.Lin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix
open CFSG.ComponentClassification CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.CGT.PushingUpLit.E3A CFSG.CGT.Timmesfeld75

variable {K : Type} [Field K]

theorem eq_one_of_conj_eq_smul_tvSL {n : ℕ} (hn : 2 ≤ n) (X : GL (Fin n) K)
    {a f : Fin n → K} (hf : f ⬝ᵥ a = 0) {c : K}
    (h : (X : Matrix (Fin n) (Fin n) K) *
        ((tvSL a f hf : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) :
    c = 1 := by
  classical
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  set T : Matrix (Fin n) (Fin n) K :=
    ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) with hTdef
  set Xm : Matrix (Fin n) (Fin n) K := ((X : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) with hXmdef
  set Xi : Matrix (Fin n) (Fin n) K := ((X⁻¹ : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) with hXidef
  have hT : T = 1 + vecMulVec a f := by rw [hTdef, coe_tvSL]
  have hXX : Xm * Xi = 1 := by
    rw [hXmdef, hXidef, ← GeneralLinearGroup.coe_mul, mul_inv_cancel,
      GeneralLinearGroup.coe_one]
  have hdet_conj : ∀ A : Matrix (Fin n) (Fin n) K, (Xm * A * Xi).det = A.det := by
    intro A
    calc (Xm * A * Xi).det = (Xm * A).det * Xi.det := by rw [Matrix.det_mul]
      _ = (Xm.det * A.det) * Xi.det := by rw [Matrix.det_mul]
      _ = A.det * (Xm.det * Xi.det) := by ring
      _ = A.det := by
        rw [← Matrix.det_mul, hXX, Matrix.det_one, mul_one]
  have hsub : Xm * (T - 1) * Xi = c • T - 1 := by
    calc Xm * (T - 1) * Xi = (Xm * T - Xm * 1) * Xi := by rw [Matrix.mul_sub]
      _ = (Xm * T - Xm) * Xi := by rw [Matrix.mul_one]
      _ = Xm * T * Xi - Xm * Xi := by rw [Matrix.sub_mul]
      _ = Xm * T * Xi - 1 := by rw [hXX]
      _ = c • T - 1 := by rw [h]
  have hdet1 : (c • T - 1).det = 0 := by
    calc (c • T - 1).det = (Xm * (T - 1) * Xi).det := by rw [hsub]
      _ = (T - 1).det := hdet_conj _
      _ = (vecMulVec a f).det := by
        rw [hT]
        simp
      _ = 0 := Matrix.det_vecMulVec a f
  by_contra hc
  have hdet2 : (c • T - 1).det = (c - 1) ^ n := by
    have he : c • T - 1 = (c - 1) • (1 : Matrix (Fin n) (Fin n) K) -
        c • vecMulVec (-a) f := by
      rw [hT, smul_add, Matrix.neg_vecMulVec, smul_neg, sub_smul, one_smul]
      abel
    rw [he]
    exact det_sub_smul_one_sub_smul_vecMulVec hc (by
      rw [dotProduct_neg, hf, neg_zero])
  have hzero : (c - 1) ^ n = 0 := by
    rw [← hdet2, hdet1]
  exact (pow_ne_zero n (sub_ne_zero.mpr hc)) hzero

theorem exists_smul_of_conjAut_fixes_tvSL {n : ℕ} (X : GL (Fin n) K)
    {a f : Fin n → K} (hf : f ⬝ᵥ a = 0)
    (h : conjAut n K X (proj n K (tvSL a f hf)) =
      proj n K (tvSL a f hf)) :
    ∃ c : K, (X : Matrix (Fin n) (Fin n) K) *
        ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *
        ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := by
  have hproj : proj n K
      (CatalogueBHigherLinearAction.slConjugation n K X (tvSL a f hf)) =
      proj n K (tvSL a f hf) := by
    simpa only [conjAut_proj] using h
  have hmem : (tvSL a f hf)⁻¹ *
      CatalogueBHigherLinearAction.slConjugation n K X (tvSL a f hf) ∈ scalars n K :=
    proj_eq_proj_iff.mp hproj.symm
  obtain ⟨c, hc, hcmat⟩ := mem_scalars.mp hmem
  have hsc : (tvSL a f hf)⁻¹ *
        CatalogueBHigherLinearAction.slConjugation n K X (tvSL a f hf) =
      scalarElement c hc := by
    apply Subtype.ext
    simpa only [coe_scalarElement] using hcmat
  have hx : CatalogueBHigherLinearAction.slConjugation n K X (tvSL a f hf) =
      tvSL a f hf * scalarElement c hc := by
    calc CatalogueBHigherLinearAction.slConjugation n K X (tvSL a f hf) =
        tvSL a f hf * ((tvSL a f hf)⁻¹ *
          CatalogueBHigherLinearAction.slConjugation n K X (tvSL a f hf)) :=
          (mul_inv_cancel_left _ _).symm
      _ = tvSL a f hf * scalarElement c hc := by rw [hsc]
  refine ⟨(c : K), ?_⟩
  calc (X : Matrix (Fin n) (Fin n) K) *
        ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *
        ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = ((CatalogueBHigherLinearAction.slConjugation n K X (tvSL a f hf) :
          SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [CatalogueBHigherLinearAction.slConjugation_matrix]
    _ = ((tvSL a f hf * scalarElement c hc :
          SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hx]
    _ = ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *
          ((scalarElement c hc : SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) := rfl
    _ = ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) * Matrix.scalar (Fin n) (c : K) := by
          rw [coe_scalarElement]
    _ = ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) * ((c : K) • (1 : Matrix (Fin n) (Fin n) K)) := by
          rw [Matrix.scalar_apply, ← smul_one_eq_diagonal]
    _ = (c : K) • ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) := by
          rw [Matrix.mul_smul, Matrix.mul_one]

theorem exists_tvCenterSL_of_conjAut_fixes_tvCenter {n : ℕ} (hn : 3 ≤ n)
    {a : Fin n → K} (ha : a ≠ 0) (X : GL (Fin n) K)
    (hfix : ∀ (f : Fin n → K) (hf : f ⬝ᵥ a = 0),
      conjAut n K X (proj n K (tvSL a f hf)) = proj n K (tvSL a f hf)) :
    ∃ S : tvCenterSL (m := n) (K := K) a,
      conjAut n K X = conjAut n K (Matrix.SpecialLinearGroup.toGL S.1) := by
  classical
  have hn2 : 2 ≤ n := by omega
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
  have hcomm : ∀ (f : Fin n → K) (hf : f ⬝ᵥ a = 0),
      ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * vecMulVec a f =
        vecMulVec a f * ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro f hf
    obtain ⟨c, hc⟩ := exists_smul_of_conjAut_fixes_tvSL X hf (hfix f hf)
    have hc1 : c = 1 := eq_one_of_conj_eq_smul_tvSL hn2 X hf hc
    have hXT : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (1 + vecMulVec a f) *
          ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 + vecMulVec a f := by
      simpa only [hc1, coe_tvSL, one_smul] using hc
    have hXXi : ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one]
    have hcommT : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (1 + vecMulVec a f) =
        (1 + vecMulVec a f) * ((X : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) := by
      have := congrArg (fun Y => Y *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hXT
      simpa only [Matrix.mul_assoc, hXXi, Matrix.mul_one] using this
    have h := hcommT
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at h
    exact add_left_cancel h
  obtain ⟨ν, w, hw, hXeq⟩ := exists_scalar_add_vecMulVec hn2 ha
    (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hcomm
  have hν : ν ≠ 0 := by
    intro hν0
    have hdet : (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 0 := by
      rw [hXeq, hν0, zero_smul, zero_add]
      exact Matrix.det_vecMulVec a w
    exact GeneralLinearGroup.det_ne_zero X hdet
  let u : Fin n → K := ν⁻¹ • w
  have hu : u ⬝ᵥ a = 0 := by
    dsimp only [u]
    rw [smul_dotProduct, hw, smul_zero]
  let S : tvCenterSL (m := n) (K := K) a := ⟨tvSL a u hu, ⟨u, hu, rfl⟩⟩
  refine ⟨S, ?_⟩
  have hSval : S.1 = tvSL a u hu := rfl
  have hXeq' : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ν •
      (S.1 :
        Matrix (Fin n) (Fin n) K) := by
    rw [hXeq, hSval, coe_tvSL, smul_add]
    congr 1
    rw [vecMulVec_smul, smul_smul, mul_inv_cancel₀ hν, one_smul]
  have hXGL : X = GeneralLinearGroup.scalar (Fin n) (Units.mk0 ν hν) *
      (Matrix.SpecialLinearGroup.toGL S.1) := by
    apply Units.ext
    change ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((GeneralLinearGroup.scalar (Fin n) (Units.mk0 ν hν) *
        (Matrix.SpecialLinearGroup.toGL S.1) :
          GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar]
    rw [hXeq']
    rw [Units.val_mk0, Matrix.scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul, SpecialLinearGroup.coe_GL_coe_matrix]
  rw [hXGL, map_mul, conjAut_scalar, one_mul]

theorem card_elemAbelian_two_aut_projSU_fixes_tvCenter [Finite K] {n : ℕ} (hn : 3 ≤ n)
    {a : Fin n → K} (ha : a ≠ 0)
    (A : Subgroup (MulAut (projectiveSL n K)))
    (hA : IsElemAbelian 2 A)
    (hfix : ∀ α ∈ A, ∀ (f : Fin n → K) (hf : f ⬝ᵥ a = 0),
      α (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K
          (CFSG.CGT.Timmesfeld75.tvSL a f hf)) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K
          (CFSG.CGT.Timmesfeld75.tvSL a f hf)) :
    Nat.card A ≤ Nat.card K ^ (n - 1) := by
  classical
  have hex : ∀ α : A, ∃ X : GL (Fin n) K,
      (α : MulAut (projectiveSL n K)) = conjAut n K X := by
    intro α
    exact eq_conjAut_of_fixes_tvCenter hn ha (α : MulAut (projectiveSL n K))
      (hfix α α.2)
  let X : A → GL (Fin n) K := fun α => Classical.choose (hex α)
  have hXα : ∀ α : A, (α : MulAut (projectiveSL n K)) = conjAut n K (X α) :=
    fun α => Classical.choose_spec (hex α)
  have hS : ∀ α : A, ∃ S : tvCenterSL (m := n) (K := K) a,
      conjAut n K (X α) = conjAut n K (Matrix.SpecialLinearGroup.toGL S.1) := by
    intro α
    refine exists_tvCenterSL_of_conjAut_fixes_tvCenter hn ha (X α) ?_
    intro f hf
    have h := hfix α α.2 f hf
    rwa [hXα α] at h
  let Sfun : A → tvCenterSL (m := n) (K := K) a := fun α => Classical.choose (hS α)
  have hSspec : ∀ α : A, conjAut n K (X α) =
      conjAut n K (Matrix.SpecialLinearGroup.toGL (Sfun α).1) :=
    fun α => Classical.choose_spec (hS α)
  have hinj : Function.Injective Sfun := by
    intro α β hαβ
    apply Subtype.ext
    calc (α : MulAut (projectiveSL n K)) = conjAut n K (X α) := hXα α
      _ = conjAut n K (Matrix.SpecialLinearGroup.toGL (Sfun α).1) := hSspec α
      _ = conjAut n K (Matrix.SpecialLinearGroup.toGL (Sfun β).1) := by rw [hαβ]
      _ = conjAut n K (X β) := (hSspec β).symm
      _ = (β : MulAut (projectiveSL n K)) := (hXα β).symm
  haveI : Finite (tvCenterSL (m := n) (K := K) a) := Subtype.finite
  calc Nat.card A ≤ Nat.card (tvCenterSL (m := n) (K := K) a) :=
        Nat.card_le_card_of_injective Sfun hinj
    _ = Nat.card K ^ (n - 1) := card_tvCenterSL ha

end CFSG.LocalAnalysis.WeakClosure81
