module

public import CFSG.CGT.Timmesfeld75.ListWCLinBasic
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix
open CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.CGT.Timmesfeld75

variable {K : Type*} [Field K] {n : ℕ}

theorem conjAut_mul_fieldAut_mul_dualAut_proj_tvSL (A : GL (Fin n) K) (σ : K ≃+* K)
    {a f : Fin n → K} (hf : f ⬝ᵥ a = 0) :
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ *
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n K)
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K
          (CFSG.CGT.Timmesfeld75.tvSL a f hf)) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K
        (CatalogueBHigherLinearAction.slConjugation n K A
          (SpecialLinearGroup.map σ.toRingHom
            ((CFSG.CGT.Timmesfeld75.tvSL a f hf)⁻¹).transpose)) := by
  show conjAut n K A (fieldAut n K σ (dualAut n K (proj n K (tvSL a f hf)))) = _
  rw [dualAut_proj, fieldAut_proj, conjAut_proj]

theorem coe_slConjugation_map_inv_transpose_tvSL (A : GL (Fin n) K) (σ : K ≃+* K)
    {a f : Fin n → K} (hf : f ⬝ᵥ a = 0) :
    ((CatalogueBHigherLinearAction.slConjugation n K A
        (SpecialLinearGroup.map σ.toRingHom ((tvSL a f hf)⁻¹).transpose)) :
        Matrix (Fin n) (Fin n) K) =
      1 - Matrix.vecMulVec ((A : Matrix (Fin n) (Fin n) K) *ᵥ
          (fun i => σ.toRingHom (f i))) ((fun i => σ.toRingHom (a i)) ᵥ*
            ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  rw [coe_slConjugation, SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.coe_transpose,
    coe_tvSL_inv hf]
  have hmap : (σ.toRingHom.mapMatrix (Matrix.vecMulVec f a)) =
      Matrix.vecMulVec (fun i => σ.toRingHom (f i)) (fun i => σ.toRingHom (a i)) := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.vecMulVec_apply]
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_vecMulVec,
    map_sub, map_one, hmap]
  have hAB : (A : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← GeneralLinearGroup.coe_mul, mul_inv_cancel, GeneralLinearGroup.coe_one]
  calc (A : Matrix (Fin n) (Fin n) K) *
        (1 - Matrix.vecMulVec (fun i => σ.toRingHom (f i))
          (fun i => σ.toRingHom (a i))) *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = (A : Matrix (Fin n) (Fin n) K) * 1 *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
        (A : Matrix (Fin n) (Fin n) K) *
          Matrix.vecMulVec (fun i => σ.toRingHom (f i))
            (fun i => σ.toRingHom (a i)) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = 1 - Matrix.vecMulVec ((A : Matrix (Fin n) (Fin n) K) *ᵥ
          (fun i => σ.toRingHom (f i))) ((fun i => σ.toRingHom (a i)) ᵥ*
            ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        rw [Matrix.mul_one, hAB, Matrix.mul_assoc, Matrix.vecMulVec_mul,
          Matrix.mul_vecMulVec]

theorem det_sub_smul_one_sub_smul_vecMulVec {c : K} (hc : c ≠ 1) {u v : Fin n → K}
    (hvu : v ⬝ᵥ u = 0) :
    (((c - 1) • (1 : Matrix (Fin n) (Fin n) K) - c • Matrix.vecMulVec u v).det =
      (c - 1) ^ n) := by
  have hc1 : c - 1 ≠ 0 := sub_ne_zero.mpr hc
  have hfac : ((c - 1) • (1 - Matrix.vecMulVec (((c - 1)⁻¹ * c) • u) v) :
      Matrix (Fin n) (Fin n) K) = (c - 1) • 1 - c • Matrix.vecMulVec u v := by
    rw [smul_sub, ← Matrix.smul_vecMulVec]
    congr 1
    rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ hc1, one_mul, Matrix.smul_vecMulVec]
  have hneg : (1 - Matrix.vecMulVec (((c - 1)⁻¹ * c) • u) v :
      Matrix (Fin n) (Fin n) K) = 1 + Matrix.vecMulVec (-(((c - 1)⁻¹ * c) • u)) v := by
    rw [Matrix.neg_vecMulVec, sub_eq_add_neg]
  have hw : v ⬝ᵥ (-(((c - 1)⁻¹ * c) • u)) = 0 := by
    rw [dotProduct_neg, dotProduct_smul, hvu, smul_zero, neg_zero]
  rw [← hfac, Matrix.det_smul, hneg, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow, hw, add_zero, mul_one,
    Fintype.card_fin]

theorem conjAut_mul_fieldAut_mul_dualAut_ne_of_fixes_tvCenter [Finite K] {n : ℕ}
    (hn : 3 ≤ n) {a : Fin n → K} (ha : a ≠ 0) (A : GL (Fin n) K) (σ : K ≃+* K) :
    ¬ (∀ (f : Fin n → K) (hf : f ⬝ᵥ a = 0),
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ *
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n K)
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K
            (CFSG.CGT.Timmesfeld75.tvSL a f hf)) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K
          (CFSG.CGT.Timmesfeld75.tvSL a f hf)) := by
  classical
  intro hfix
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨i, hi⟩ : ∃ i : Fin n, a i ≠ 0 := Function.ne_iff.mp ha
  have hcard : 1 < (Finset.univ.erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hcard
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hki : k ≠ i := (Finset.mem_erase.mp hk).1
  have hkj : k ≠ j := fun h => hjk h.symm
  let sa : Fin n → K := fun t => σ.toRingHom (a t)
  let v : Fin n → K := sa ᵥ* ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hBA : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (A : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one]
  have hsa : sa ≠ 0 := by
    intro h0
    apply ha
    funext t
    exact σ.injective (by simpa [sa] using congrFun h0 t)
  have hv : v ≠ 0 := by
    intro hv0
    have hv_eq : v = ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ sa := by
      simp only [v]
      exact (Matrix.mulVec_transpose _ _).symm
    have hcomp : ((A : Matrix (Fin n) (Fin n) K))ᵀ *ᵥ v = sa := by
      rw [hv_eq, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hBA, Matrix.transpose_one,
        Matrix.one_mulVec]
    apply hsa
    rw [← hcomp, hv0, Matrix.mulVec_zero]
  have key : ∀ (f : Fin n → K) (hf : f ⬝ᵥ a = 0), ∃ μ : K, f = μ • v := by
    intro f hf
    let sf : Fin n → K := fun t => σ.toRingHom (f t)
    let u : Fin n → K := (A : Matrix (Fin n) (Fin n) K) *ᵥ sf
    have hvu : v ⬝ᵥ u = 0 := by
      have hdot : sa ⬝ᵥ sf = 0 := by
        have h := congrArg σ.toRingHom hf
        rw [RingHom.map_dotProduct, dotProduct_comm] at h
        simpa only [map_zero, sa, sf, Function.comp_def] using h
      simp only [v, u, sa, sf] at hdot ⊢
      rw [dotProduct_mulVec, vecMul_vecMul, hBA, Matrix.vecMul_one, hdot]
    have himg := conjAut_mul_fieldAut_mul_dualAut_proj_tvSL (n := n) A σ hf
    have hmat := coe_slConjugation_map_inv_transpose_tvSL (n := n) A σ hf
    have hproj2 : proj n K (CatalogueBHigherLinearAction.slConjugation n K A
        (SpecialLinearGroup.map σ.toRingHom ((tvSL a f hf)⁻¹).transpose)) =
        proj n K (tvSL a f hf) := by
      rw [← himg]
      exact hfix f hf
    obtain ⟨c, hc, hcm⟩ := mem_scalars.mp (proj_eq_proj_iff.mp hproj2)
    set Nsl : SpecialLinearGroup (Fin n) K :=
      CatalogueBHigherLinearAction.slConjugation n K A
        (SpecialLinearGroup.map σ.toRingHom ((tvSL a f hf)⁻¹).transpose) with hNsl
    have hsc : Nsl⁻¹ * tvSL a f hf = scalarElement c hc := Subtype.ext hcm
    have hM : tvSL a f hf = Nsl * scalarElement c hc := by
      calc tvSL a f hf = Nsl * (Nsl⁻¹ * tvSL a f hf) := (mul_inv_cancel_left Nsl _).symm
        _ = Nsl * scalarElement c hc := by rw [hsc]
    have hmatM : ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
        ((Nsl : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          Matrix.scalar (Fin n) (c : K) := by
      have h := congrArg (fun x : SpecialLinearGroup (Fin n) K =>
        (x : Matrix (Fin n) (Fin n) K)) hM
      simpa [hNsl] using h
    have hNM : ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (c : K) • (1 - Matrix.vecMulVec u v) := by
      calc ((tvSL a f hf : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
          = ((Nsl : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              Matrix.scalar (Fin n) (c : K) := hmatM
        _ = ((Nsl : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((c : K) • (1 : Matrix (Fin n) (Fin n) K)) := by
            rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
        _ = (c : K) • (((Nsl : SpecialLinearGroup (Fin n) K) :
              Matrix (Fin n) (Fin n) K) * 1) := by rw [Matrix.mul_smul]
        _ = (c : K) • (1 - Matrix.vecMulVec u v) := by
            rw [Matrix.mul_one, hNsl, hmat]
    have hX : ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) - 1 = (c : K) • (1 : Matrix (Fin n) (Fin n) K) -
          (c : K) • Matrix.vecMulVec u v - 1 := by
      rw [hNM, smul_sub]
    have hX' : ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) - 1 = ((c : K) - 1) •
          (1 : Matrix (Fin n) (Fin n) K) - (c : K) • Matrix.vecMulVec u v := by
      rw [hX, sub_smul, one_smul]
      abel
    have hdetL : (((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) - 1).det = 0 := by
      rw [coe_tvSL hf]
      simpa using Matrix.det_vecMulVec a f
    have hc1 : (c : K) = 1 := by
      by_contra hcne
      have hdet := det_sub_smul_one_sub_smul_vecMulVec (n := n) hcne hvu
      rw [← hX', hdetL] at hdet
      have hpow : (c : K) - 1 = 0 := by
        have hn0 : n ≠ 0 := by omega
        exact (pow_eq_zero_iff hn0).mp hdet.symm
      exact hcne (sub_eq_zero.mp hpow)
    have hNM1 : ((tvSL a f hf : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 - Matrix.vecMulVec u v := by
      rw [hNM, hc1, one_smul]
    have hvec : Matrix.vecMulVec (-u) v = Matrix.vecMulVec a f := by
      have h := congrArg (fun X : Matrix (Fin n) (Fin n) K => X - 1) hNM1
      rw [coe_tvSL hf] at h
      have h' : Matrix.vecMulVec a f = -Matrix.vecMulVec u v := by simpa using h
      rw [Matrix.neg_vecMulVec, h']
    obtain ⟨μ, -, hμ⟩ := exists_smul_of_vecMulVec_eq hvec ha hv
    exact ⟨μ, hμ⟩
  let f : Fin n → K := Pi.single j 1 - Pi.single i (a j / a i)
  let g : Fin n → K := Pi.single k 1 - Pi.single i (a k / a i)
  have hf : f ⬝ᵥ a = 0 := by
    simp only [f, sub_dotProduct, single_dotProduct]
    field_simp
    ring
  have hg : g ⬝ᵥ a = 0 := by
    simp only [g, sub_dotProduct, single_dotProduct]
    field_simp
    ring
  obtain ⟨μ, hμ⟩ := key f hf
  obtain ⟨ν, hν⟩ := key g hg
  have hfj : f j = 1 := by simp [f, hji]
  have hgj : g j = 0 := by simp [g, hji, hkj]
  have hgk : g k = 1 := by simp [g, hki, hkj]
  have h1 : (1 : K) = μ * v j := by
    have := congrFun hμ j
    simpa [hfj, Pi.smul_apply, smul_eq_mul] using this
  have h2 : (0 : K) = ν * v j := by
    have := congrFun hν j
    simpa [hgj, Pi.smul_apply, smul_eq_mul] using this
  have h3 : (1 : K) = ν * v k := by
    have := congrFun hν k
    simpa [hgk, Pi.smul_apply, smul_eq_mul] using this
  rcases mul_eq_zero.mp h2.symm with hν0 | hvj0
  · rw [hν0, zero_mul] at h3
    exact zero_ne_one h3.symm
  · rw [hvj0, mul_zero] at h1
    exact zero_ne_one h1.symm

end CFSG.LocalAnalysis.WeakClosure81
