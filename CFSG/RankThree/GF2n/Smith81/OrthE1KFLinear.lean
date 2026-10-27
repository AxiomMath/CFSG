module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps
import CFSG.RankThree.GF2n.Stroth80.Hom24Omega
import CFSG.RankThree.GF2n.Stroth80.Hom24Minus

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.Open QuadraticMap

namespace KFLin

section Matrices

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem matrix_eq_of_dotProduct {M N : Matrix ι ι K}
    (h : ∀ v w : ι → K, v ⬝ᵥ (M *ᵥ w) = v ⬝ᵥ (N *ᵥ w)) : M = N := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single_one] using this

theorem mulVec_dotProduct' (a : Matrix ι ι K) (v x : ι → K) :
    (a *ᵥ v) ⬝ᵥ x = v ⬝ᵥ (aᵀ *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem dotProduct_conj (a J : Matrix ι ι K) (v w : ι → K) :
    (a *ᵥ v) ⬝ᵥ (J *ᵥ (a *ᵥ w)) = v ⬝ᵥ ((aᵀ * J * a) *ᵥ w) := by
  rw [mulVec_dotProduct', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem dotProduct_ofMul (u v w : ι → K) :
    v ⬝ᵥ (Matrix.of (fun i j => u i * u j) *ᵥ w) = (u ⬝ᵥ v) * (u ⬝ᵥ w) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem isometry_of_mem_statedOmega {f : (ι → K) → K} {g : GL ι K} (hg : g ∈ StatedOmega f)
    (v : ι → K) : f ((g : Matrix ι ι K) *ᵥ v) = f v := by
  let I : Subgroup (GL ι K) :=
    { carrier := {A | ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = f v}
      one_mem' := fun v => by simp
      mul_mem' := fun {a b} ha hb v => by
        simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
        rw [ha, hb]
      inv_mem' := fun {a} ha v => by
        have := ha (((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
        simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this.symm }
  have hcl : Subgroup.closure {A : GL ι K | ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = f v} ≤ I :=
    (Subgroup.closure_le I).mpr fun A hA => hA
  have hg' : g ∈ Subgroup.closure {A : GL ι K | ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = f v} :=
    Subgroup.commutator_le_self _ hg
  exact hcl hg' v

end Matrices

section Gram

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem polarGram_eq_toMatrix₂' (Q : QuadraticForm K (ι → K)) :
    polarGram ⇑Q = LinearMap.toMatrix₂' K (polarBilin Q) := by
  ext i j
  simp [polarGram, polarFn, LinearMap.toMatrix₂'_apply, polar]

theorem polar_eq_dotProduct (Q : QuadraticForm K (ι → K)) (v w : ι → K) :
    polar Q v w = v ⬝ᵥ (polarGram ⇑Q *ᵥ w) := by
  rw [polarGram_eq_toMatrix₂', ← Matrix.toLinearMap₂'_apply' (T := K)]
  simp

theorem isUnit_det_polarGram {Q : QuadraticForm K (ι → K)} (hnd : (polarBilin Q).Nondegenerate) :
    IsUnit (polarGram ⇑Q).det := by
  have hJnd : (polarGram ⇑Q).Nondegenerate := by
    refine ⟨Matrix.separatingLeft_def.mpr fun v hv => ?_,
      Matrix.separatingRight_def.mpr fun w hw => ?_⟩
    · exact hnd.1 v fun w => by rw [polarBilin_apply_apply, polar_eq_dotProduct]; exact hv w
    · exact hnd.2 w fun v => by rw [polarBilin_apply_apply, polar_eq_dotProduct]; exact hw v
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp hJnd)

theorem polarGram_diag [CharP K 2] (Q : QuadraticForm K (ι → K)) (i : ι) :
    polarGram ⇑Q i i = 0 := by
  have h := polar_eq_dotProduct Q (Pi.single i 1) (Pi.single i 1)
  rw [QuadraticMap.polar_self] at h
  have h2 : (2 : ℕ) • Q (Pi.single i 1) = 0 := by
    rw [two_nsmul]
    exact CharTwo.add_self_eq_zero _
  simpa [Matrix.mulVec_single_one, h2, eq_comm] using h

theorem polar_mulVec {Q : QuadraticForm K (ι → K)} {g : Matrix ι ι K}
    (hg : ∀ v, Q (g *ᵥ v) = Q v) (v w : ι → K) :
    polar Q (g *ᵥ v) (g *ᵥ w) = polar Q v w := by
  simp only [polar]
  rw [← Matrix.mulVec_add, hg, hg, hg]

theorem gram_invariant {Q : QuadraticForm K (ι → K)} {g : Matrix ι ι K}
    (hg : ∀ v, Q (g *ᵥ v) = Q v) : gᵀ * polarGram ⇑Q * g = polarGram ⇑Q := by
  apply matrix_eq_of_dotProduct
  intro v w
  have h := polar_mulVec hg v w
  rw [polar_eq_dotProduct, polar_eq_dotProduct] at h
  rw [← h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_dotProduct']

end Gram

section NatIrred

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem commutant_scalar_of_linear {f₀ : (ι → K) → K}
    (h : ∀ f : (ι → K) →ₗ[K] (ι → K),
      (∀ A ∈ StatedOmega f₀, ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = (A : Matrix ι ι K) *ᵥ f v) →
        ∃ c : K, ∀ v, f v = c • v) :
    ∀ A : Matrix ι ι K,
      (∀ g ∈ StatedOmega f₀, A * (g : Matrix ι ι K) = (g : Matrix ι ι K) * A) →
        ∃ c : K, A = c • (1 : Matrix ι ι K) := by
  intro A hA
  obtain ⟨c, hc⟩ := h (Matrix.toLin' A) (fun g hg v => by
    simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hA g hg])
  refine ⟨c, ?_⟩
  ext i j
  have := congrFun (hc (Pi.single j 1)) i
  simpa [Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply,
    eq_comm] using this

theorem natIrredFor_of_form {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hnd : (polarBilin Q).Nondegenerate)
    (hcomm : ∀ A : Matrix ι ι K,
      (∀ g ∈ StatedOmega Q₀, A * (g : Matrix ι ι K) = (g : Matrix ι ι K) * A) →
        ∃ c : K, A = c • (1 : Matrix ι ι K)) :
    NatIrredFor K Q₀ := by
  subst hQ
  refine ⟨hcomm, ?_⟩
  intro b hb
  set J := polarGram ⇑Q with hJ
  have hdet : IsUnit J.det := isUnit_det_polarGram hnd
  have hJinv : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hdet
  have hJJinv : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hdet
  have hcomm' : ∀ g ∈ StatedOmega ⇑Q, (J⁻¹ * b) * (g : Matrix ι ι K) =
      (g : Matrix ι ι K) * (J⁻¹ * b) := by
    intro g hg
    have hJg : (g : Matrix ι ι K)ᵀ * J * g = J := gram_invariant (isometry_of_mem_statedOmega hg)
    have hbg := hb g hg
    set h := ((g⁻¹ : GL ι K) : Matrix ι ι K) with hh
    have hgh : (g : Matrix ι ι K) * h = 1 := by rw [hh, ← Units.val_mul, mul_inv_cancel]; rfl
    have h1 : b * g = hᵀ * b := by
      calc b * g = (hᵀ * (g : Matrix ι ι K)ᵀ) * b * g := by
            rw [← Matrix.transpose_mul, hgh, Matrix.transpose_one, Matrix.one_mul]
        _ = hᵀ * ((g : Matrix ι ι K)ᵀ * b * g) := by simp only [Matrix.mul_assoc]
        _ = hᵀ * b := by rw [hbg]
    have h2 : J * g = hᵀ * J := by
      calc J * g = (hᵀ * (g : Matrix ι ι K)ᵀ) * J * g := by
            rw [← Matrix.transpose_mul, hgh, Matrix.transpose_one, Matrix.one_mul]
        _ = hᵀ * ((g : Matrix ι ι K)ᵀ * J * g) := by simp only [Matrix.mul_assoc]
        _ = hᵀ * J := by rw [hJg]
    have h3 : (g : Matrix ι ι K) * J⁻¹ = J⁻¹ * hᵀ := by
      calc (g : Matrix ι ι K) * J⁻¹ = J⁻¹ * (J * g) * J⁻¹ := by
            rw [← Matrix.mul_assoc, hJinv, Matrix.one_mul]
        _ = J⁻¹ * (hᵀ * J) * J⁻¹ := by rw [h2]
        _ = J⁻¹ * hᵀ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hJJinv, Matrix.mul_one]
    calc (J⁻¹ * b) * (g : Matrix ι ι K) = J⁻¹ * (b * g) := by rw [Matrix.mul_assoc]
      _ = J⁻¹ * (hᵀ * b) := by rw [h1]
      _ = (J⁻¹ * hᵀ) * b := by rw [Matrix.mul_assoc]
      _ = ((g : Matrix ι ι K) * J⁻¹) * b := by rw [h3]
      _ = (g : Matrix ι ι K) * (J⁻¹ * b) := by rw [Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := hcomm _ hcomm'
  refine ⟨c, ?_⟩
  calc b = J * (J⁻¹ * b) := by rw [← Matrix.mul_assoc, hJJinv, Matrix.one_mul]
    _ = J * (c • (1 : Matrix ι ι K)) := by rw [hc]
    _ = c • J := by simp

theorem natIrredFor_plus (K : Type) [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    NatIrredFor K (StatedQuadPlus 2 K) :=
  natIrredFor_of_form (CFSG.LieType.Universal.Spin.coe_quadPlus 2 K)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 2 K)
    (commutant_scalar_of_linear fun f hf =>
      CFSG.RankThree.GF2n.Stroth80.stroth_2_4_omegaPlus K hK 2 le_rfl f hf)

theorem natIrredFor_minus (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    NatIrredFor K (StatedQuadMinus 2 K b c) :=
  natIrredFor_of_form (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr)
    (commutant_scalar_of_linear fun f hf =>
      CFSG.RankThree.GF2n.Stroth80.stroth_2_4_omegaMinus K (m := 2) le_rfl hirr f hf)

end NatIrred

section Normalizer

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem normalizerOmegaFor_of_form [Finite K] [CharP K 2] [Nonempty ι]
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hnd : (polarBilin Q).Nondegenerate) (hirr : NatIrredFor K Q₀) :
    NormalizerOmegaFor K Q₀ := by
  subst hQ
  intro A hN
  classical
  set J := polarGram ⇑Q with hJ
  set a : Matrix ι ι K := (A : Matrix ι ι K) with ha
  let sqrt : K ≃+* K := (frobeniusEquiv K 2).symm
  have hsqrt_sq : ∀ x : K, (sqrt x) ^ 2 = x := by
    intro x
    have h := (frobeniusEquiv K 2).apply_symm_apply x
    rwa [frobeniusEquiv_def] at h
  have hsqrt_sq_apply : ∀ x : K, sqrt (x ^ 2) = x := by
    intro x
    rw [← frobeniusEquiv_def (R := K) (p := 2) x, RingEquiv.symm_apply_apply]
  have hinv : ∀ g ∈ StatedOmega ⇑Q, ∀ v,
      Q (a *ᵥ ((g : Matrix ι ι K) *ᵥ v)) = Q (a *ᵥ v) := by
    intro g hg v
    have hω := isometry_of_mem_statedOmega (hN g hg) (a *ᵥ v)
    have h : ((A * g * A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ (a *ᵥ v) =
        a *ᵥ ((g : Matrix ι ι K) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      simp only [Units.val_mul, ha, Matrix.mul_assoc]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [← h]
    exact hω
  set b : Matrix ι ι K := aᵀ * J * a with hb
  have hbinv : ∀ g ∈ StatedOmega ⇑Q,
      (g : Matrix ι ι K)ᵀ * b * (g : Matrix ι ι K) = b := by
    intro g hg
    apply matrix_eq_of_dotProduct
    intro v w
    have hpol : polar Q (a *ᵥ ((g : Matrix ι ι K) *ᵥ v)) (a *ᵥ ((g : Matrix ι ι K) *ᵥ w)) =
        polar Q (a *ᵥ v) (a *ᵥ w) := by
      simp only [polar, ← Matrix.mulVec_add, hinv g hg]
    have e1 : polar Q (a *ᵥ ((g : Matrix ι ι K) *ᵥ v)) (a *ᵥ ((g : Matrix ι ι K) *ᵥ w)) =
        v ⬝ᵥ (((g : Matrix ι ι K)ᵀ * b * (g : Matrix ι ι K)) *ᵥ w) := by
      rw [polar_eq_dotProduct, dotProduct_conj, dotProduct_conj]
    have e2 : polar Q (a *ᵥ v) (a *ᵥ w) = v ⬝ᵥ (b *ᵥ w) := by
      rw [polar_eq_dotProduct, dotProduct_conj]
    rw [← e1, ← e2, hpol]
  obtain ⟨c, hc⟩ := hirr.2 b hbinv
  have hdetJ : IsUnit J.det := isUnit_det_polarGram hnd
  have hdeta : IsUnit a.det := (Matrix.isUnit_iff_isUnit_det a).mp A.isUnit
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h : IsUnit b.det := by
      rw [hb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      exact (hdeta.mul hdetJ).mul hdeta
    rw [hc, zero_smul] at h
    simp at h
  have hpolar : ∀ v w, polar Q (a *ᵥ v) (a *ᵥ w) = c * polar Q v w := by
    intro v w
    rw [polar_eq_dotProduct, polar_eq_dotProduct, dotProduct_conj, ← hb, hc]
    simp [Matrix.smul_mulVec, dotProduct_smul]
  let D : (ι → K) → K := fun v => Q (a *ᵥ v) - c * Q v
  have hDadd : ∀ u w, D (u + w) = D u + D w := by
    intro u w
    have h1 : Q (a *ᵥ (u + w)) = Q (a *ᵥ u) + Q (a *ᵥ w) + c * polar Q u w := by
      rw [Matrix.mulVec_add, QuadraticMap.map_add Q (a *ᵥ u) (a *ᵥ w), hpolar]
    have h2 : Q (u + w) = Q u + Q w + polar Q u w := QuadraticMap.map_add Q u w
    simp only [D, h1, h2]
    ring
  have hDsmul : ∀ r v, D (r • v) = r ^ 2 * D v := by
    intro r v
    simp only [D, Matrix.mulVec_smul, QuadraticMap.map_smul, smul_eq_mul]
    ring
  have hDinv : ∀ g ∈ StatedOmega ⇑Q, ∀ v, D ((g : Matrix ι ι K) *ᵥ v) = D v := by
    intro g hg v
    simp only [D, hinv g hg, isometry_of_mem_statedOmega hg]
  let L : (ι → K) →ₗ[K] K :=
    { toFun := fun v => sqrt (D v)
      map_add' := fun u w => by rw [hDadd, map_add]
      map_smul' := fun r v => by
        rw [hDsmul, map_mul, hsqrt_sq_apply, smul_eq_mul, RingHom.id_apply] }
  have hLinv : ∀ g ∈ StatedOmega ⇑Q, ∀ v, L ((g : Matrix ι ι K) *ᵥ v) = L v := by
    intro g hg v
    show sqrt (D _) = sqrt (D v)
    rw [hDinv g hg v]
  have hL0 : ∀ v, L v = 0 := by
    set u : ι → K := fun i => L (Pi.single i 1) with hu
    have hLu : ∀ v, L v = u ⬝ᵥ v := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ L v]
      simp only [dotProduct, hu, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
      congr 2
      ext j
      simp [Pi.single_apply, eq_comm]
    have hMinv : ∀ g ∈ StatedOmega ⇑Q, (g : Matrix ι ι K)ᵀ * Matrix.of (fun i j => u i * u j) *
        (g : Matrix ι ι K) = Matrix.of (fun i j => u i * u j) := by
      intro g hg
      apply matrix_eq_of_dotProduct
      intro v w
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← mulVec_dotProduct',
        dotProduct_ofMul, dotProduct_ofMul, ← hLu, ← hLu, ← hLu, ← hLu, hLinv g hg, hLinv g hg]
    obtain ⟨c₁, hc₁⟩ := hirr.2 _ hMinv
    have hdiag : ∀ i, u i = 0 := by
      intro i
      have h := congrFun (congrFun hc₁ i) i
      rw [Matrix.of_apply, Matrix.smul_apply, polarGram_diag, smul_zero] at h
      exact mul_self_eq_zero.mp h
    intro v
    rw [hLu v, show u = 0 from funext hdiag]
    simp
  have hD0 : ∀ v, Q (a *ᵥ v) = c * Q v := by
    intro v
    have h1 : D v = (L v) ^ 2 := by
      show D v = (sqrt (D v)) ^ 2
      rw [hsqrt_sq]
    rw [hL0 v] at h1
    have h2 : D v = 0 := by simpa using h1
    simpa [D, sub_eq_zero] using h2
  have hs0 : sqrt c ≠ 0 := by
    intro h
    apply hc0
    rw [← hsqrt_sq c, h]
    simp
  refine ⟨(sqrt c)⁻¹, inv_ne_zero hs0, fun v => ?_⟩
  rw [QuadraticMap.map_smul, smul_eq_mul, hD0 v]
  have hs : (sqrt c) ^ 2 = c := hsqrt_sq c
  have h : (sqrt c)⁻¹ * (sqrt c)⁻¹ * c = 1 := by
    calc (sqrt c)⁻¹ * (sqrt c)⁻¹ * c = (sqrt c)⁻¹ * (sqrt c)⁻¹ * (sqrt c) ^ 2 := by rw [hs]
      _ = 1 := by field_simp
  calc (sqrt c)⁻¹ * (sqrt c)⁻¹ * (c * Q v) = ((sqrt c)⁻¹ * (sqrt c)⁻¹ * c) * Q v := by ring
    _ = Q v := by rw [h, one_mul]

theorem normalizerOmegaFor_plus (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) : NormalizerOmegaFor K (StatedQuadPlus 2 K) :=
  normalizerOmegaFor_of_form (CFSG.LieType.Universal.Spin.coe_quadPlus 2 K)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 2 K) (natIrredFor_plus K hK)

theorem normalizerOmegaFor_minus (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    NormalizerOmegaFor K (StatedQuadMinus 2 K b c) :=
  normalizerOmegaFor_of_form (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr)
    (natIrredFor_minus K b c hirr)

end Normalizer

section Parabolic

variable {K : Type} [Field K] (S : QSpace K)

theorem B_swap (e f : S.E) : S.B f e = - S.B e f := by
  have h := S.alt (e + f)
  simp only [map_add, LinearMap.add_apply, S.alt] at h
  linear_combination h

theorem B_eq_Qf (e f : S.E) : S.B e f = S.Qf (e + f) - S.Qf e - S.Qf f := by
  rw [S.Qf_add]
  ring

theorem B_zero_of_isTS {V : Submodule K S.E} (hV : S.IsTS V) {v w : S.E} (hv : v ∈ V)
    (hw : w ∈ V) : S.B v w = 0 := by
  rw [B_eq_Qf, hV (v + w) (V.add_mem hv hw), hV v hv, hV w hw]
  ring

theorem B_isometry {g : S.E ≃ₗ[K] S.E} (hg : g ∈ S.O) (e f : S.E) :
    S.B (g e) (g f) = S.B e f := by
  have hg' : ∀ x, S.Qf (g x) = S.Qf x := hg
  rw [B_eq_Qf, B_eq_Qf, ← map_add, hg', hg', hg']

theorem B_nondegenerate : S.B.Nondegenerate :=
  ⟨fun e he => S.nondeg e he, fun f hf => S.nondeg f fun e => by rw [B_swap, hf e, neg_zero]⟩

theorem perp_le {V : Submodule K S.E} (hV : S.IsTS V) (h8 : Module.finrank K S.E = 8)
    (h4 : Module.finrank K V = 4) : ∀ e, (∀ v ∈ V, S.B e v = 0) → e ∈ V := by
  have hle : V ≤ LinearMap.BilinForm.orthogonal S.B V := fun v hv n hn =>
    B_zero_of_isTS S hV hn hv
  have hfin : Module.finrank K (LinearMap.BilinForm.orthogonal S.B V) = 4 := by
    rw [LinearMap.BilinForm.finrank_orthogonal (B_nondegenerate S) V, h8, h4]
  have heq : V = LinearMap.BilinForm.orthogonal S.B V :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, h4])
  intro e he
  have h : e ∈ LinearMap.BilinForm.orthogonal S.B V := fun n hn => by
    rw [B_swap, he n hn, neg_zero]
  rwa [← heq] at h

def qspaceQuad : QuadraticMap K S.E K where
  toFun := S.Qf
  toFun_smul := fun a x => by simp only [S.Qf_smul, smul_eq_mul]; ring
  exists_companion' := ⟨S.B, S.Qf_add⟩

theorem exists_isCompl_isTS {V : Submodule K S.E} (hV : S.IsTS V)
    (h8 : Module.finrank K S.E = 8) (h4 : Module.finrank K V = 4) :
    ∃ V' : Submodule K S.E, IsCompl V V' ∧ S.IsTS V' := by
  have hperp := perp_le S hV h8 h4
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  have hdec : ∀ e : S.E, ∃ v ∈ V, ∃ w ∈ W, v + w = e := fun e => by
    obtain ⟨v, hv, w, hw, h⟩ :=
      Submodule.mem_sup.mp (hW.sup_eq_top ▸ Submodule.mem_top (x := e))
    exact ⟨v, hv, w, hw, h⟩
  have hWdim : Module.finrank K W = 4 := by
    have := Submodule.finrank_add_eq_of_isCompl hW
    omega
  let Ψ : V →ₗ[K] Module.Dual K W :=
    (LinearMap.lcomp K K W.subtype) ∘ₗ S.B.flip ∘ₗ V.subtype
  have hΨ : ∀ (v : V) (w : W), Ψ v w = S.B (w : S.E) (v : S.E) := fun v w => rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    apply Subtype.ext
    refine S.nondeg _ fun e => ?_
    obtain ⟨v', hv', w, hw, rfl⟩ := hdec e
    rw [map_add, B_swap S v' (v : S.E), B_swap S w (v : S.E)]
    have h1 : S.B v' (v : S.E) = 0 := B_zero_of_isTS S hV hv' v.2
    have h2 : S.B w (v : S.E) = 0 := by
      have := LinearMap.congr_fun hv ⟨w, hw⟩
      simpa [hΨ] using this
    simp [h1, h2]
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq, hWdim]; exact h4)).mp hinj
  let Ψe : V ≃ₗ[K] Module.Dual K W := LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  obtain ⟨β, hβ⟩ := LinearMap.BilinMap.toQuadraticMap_surjective
    ((qspaceQuad S).comp W.subtype)
  have hβdiag : ∀ w : W, β w w = S.Qf (w : S.E) := fun w => by
    have := congrArg (fun q => q w) hβ
    simpa [qspaceQuad] using this
  let φ : W →ₗ[K] V := Ψe.symm.toLinearMap ∘ₗ (-β.flip)
  have hφ : ∀ w w' : W, S.B (w : S.E) (φ w' : S.E) = - β w w' := fun w w' => by
    have h := LinearMap.congr_fun (Ψe.apply_symm_apply ((-β.flip) w')) w
    have e : (Ψe (Ψe.symm ((-β.flip) w'))) w =
        S.B (w : S.E) ((Ψe.symm ((-β.flip) w') : V) : S.E) := rfl
    rw [e] at h
    exact h.trans (by simp)
  let θ : W →ₗ[K] S.E := W.subtype + V.subtype ∘ₗ φ
  have hθ : ∀ w : W, θ w = (w : S.E) + (φ w : S.E) := fun w => rfl
  refine ⟨LinearMap.range θ, ⟨?_, ?_⟩, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨w, rfl⟩
    have hwV : (w : S.E) ∈ V := by
      have := V.sub_mem hx (φ w).2
      simpa [hθ] using this
    have hw0 : (w : S.E) = 0 := Submodule.disjoint_def.mp hW.disjoint (w : S.E) hwV w.2
    have : w = 0 := Subtype.ext hw0
    simp [this]
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro e
    obtain ⟨v, hv, w, hw, rfl⟩ := hdec e
    refine Submodule.mem_sup.mpr ⟨v - (φ ⟨w, hw⟩ : S.E), V.sub_mem hv (φ ⟨w, hw⟩).2,
      θ ⟨w, hw⟩, ⟨_, rfl⟩, ?_⟩
    simp [hθ]
  · rintro _ ⟨w, rfl⟩
    rw [hθ, S.Qf_add, hV _ (φ w).2, hφ w w, hβdiag w]
    ring

theorem U_iff {V : Submodule K S.E} (hV : S.IsTS V)
    (hperp : ∀ e, (∀ v ∈ V, S.B e v = 0) → e ∈ V) (g : S.E ≃ₗ[K] S.E) :
    g ∈ S.U V ↔ ∃ β : S.E →ₗ[K] S.E, (∀ e, β e ∈ V) ∧ (∀ v ∈ V, β v = 0) ∧
      (∀ e, S.B e (β e) = 0) ∧ ∀ e, g e = e + β e := by
  constructor
  · rintro ⟨hgO, hgV⟩
    have hgO' : ∀ x, S.Qf (g x) = S.Qf x := hgO
    have hrange : ∀ e, g e - e ∈ V := by
      intro e
      apply hperp
      intro v hv
      have h1 : S.B (g e) v = S.B e v := by
        have := B_isometry S hgO e v
        rwa [hgV v hv] at this
      rw [map_sub, LinearMap.sub_apply, h1, sub_self]
    refine ⟨(g : S.E →ₗ[K] S.E) - LinearMap.id, hrange, ?_, ?_, ?_⟩
    · intro v hv
      simp [hgV v hv]
    · intro e
      have hx : S.Qf (g e - e) = 0 := hV _ (hrange e)
      have h := S.Qf_add e (g e - e)
      rw [add_sub_cancel, hgO' e, hx] at h
      show S.B e (g e - e) = 0
      linear_combination -h
    · intro e
      simp
  · rintro ⟨β, hrange, hkill, halt, hge⟩
    refine ⟨?_, fun v hv => ?_⟩
    · show ∀ e, S.Qf (g e) = S.Qf e
      intro e
      rw [hge e, S.Qf_add, hV _ (hrange e), halt e]
      ring
    · rw [hge v, hkill v hv, add_zero]

theorem exists_U {V : Submodule K S.E} (hV : S.IsTS V)
    (hperp : ∀ e, (∀ v ∈ V, S.B e v = 0) → e ∈ V) (β : S.E →ₗ[K] S.E)
    (hrange : ∀ e, β e ∈ V) (hkill : ∀ v ∈ V, β v = 0) (halt : ∀ e, S.B e (β e) = 0) :
    ∃ g ∈ S.U V, ∀ e, g e = e + β e := by
  have hβ2 : ∀ e, β (β e) = 0 := fun e => hkill _ (hrange e)
  let g : S.E ≃ₗ[K] S.E := LinearEquiv.ofLinear (LinearMap.id + β) (LinearMap.id - β)
    (by ext e; simp [hβ2]) (by ext e; simp [hβ2])
  have hg : ∀ e, g e = e + β e := fun e => by simp [g]
  exact ⟨g, (U_iff S hV hperp g).mpr ⟨β, hrange, hkill, halt, hg⟩, hg⟩

end Parabolic

end KFLin

theorem parabolic_holds : ParabolicStatement := by
  unfold ParabolicStatement
  intro K _ _ _ _ S h8 _ V hV h4
  have hperp := KFLin.perp_le S hV h8 h4
  exact ⟨hperp, KFLin.exists_isCompl_isTS S hV h8 h4, fun g => KFLin.U_iff S hV hperp g,
    fun β hr hk ha => KFLin.exists_U S hV hperp β hr hk ha⟩

theorem natIrred_holds : NatIrredStatement := by
  unfold NatIrredStatement ForBothSigns
  intro K _ _ _ hK
  exact ⟨KFLin.natIrredFor_plus K hK, fun b c hirr => KFLin.natIrredFor_minus K b c hirr⟩

theorem normalizerOmega_holds : NormalizerOmegaStatement := by
  unfold NormalizerOmegaStatement ForBothSigns
  intro K _ _ _ hK
  exact ⟨KFLin.normalizerOmegaFor_plus K hK,
    fun b c hirr => KFLin.normalizerOmegaFor_minus K b c hirr⟩

end CFSG.RankThree.GF2n.Smith81.Smith23E1
