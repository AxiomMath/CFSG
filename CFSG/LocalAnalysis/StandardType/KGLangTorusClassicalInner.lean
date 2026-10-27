module

public import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUSpLabels
import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private noncomputable def kgLangCInnerAux_conjPowElem {ι : Type} [Fintype ι] [DecidableEq ι] {𝕂 : Type}
    [Field 𝕂] (H : Subgroup (Matrix.GeneralLinearGroup ι 𝕂))
    (A : Matrix.GeneralLinearGroup ι 𝕂)
    (hH : ∀ h : ↥H, A * (↑h : Matrix.GeneralLinearGroup ι 𝕂) * A⁻¹ ∈ H) (k : ℕ) (h : ↥H) : ↥H :=
  ⟨A ^ k * (↑h : Matrix.GeneralLinearGroup ι 𝕂) * (A ^ k)⁻¹, by
    induction k with
    | zero => simpa using h.2
    | succ k ih =>
        have hmem : A * (A ^ k * (↑h : Matrix.GeneralLinearGroup ι 𝕂) * (A ^ k)⁻¹) * A⁻¹ ∈ H :=
          hH ⟨A ^ k * (↑h : Matrix.GeneralLinearGroup ι 𝕂) * (A ^ k)⁻¹, ih⟩
        have heq : A * (A ^ k * (↑h : Matrix.GeneralLinearGroup ι 𝕂) * (A ^ k)⁻¹) * A⁻¹ =
            A ^ (k + 1) * (↑h : Matrix.GeneralLinearGroup ι 𝕂) * (A ^ (k + 1))⁻¹ := by
          rw [pow_succ']
          group
        rwa [heq] at hmem⟩

private theorem kgLangCInnerAux_pow_apply {ι : Type} [Fintype ι] [DecidableEq ι] {𝕂 : Type}
    [Field 𝕂] (H : Subgroup (Matrix.GeneralLinearGroup ι 𝕂))
    (A : Matrix.GeneralLinearGroup ι 𝕂)
    (hH : ∀ h : ↥H, A * (↑h : Matrix.GeneralLinearGroup ι 𝕂) * A⁻¹ ∈ H)
    {R : Type} [Group R] {π : ↥H →* R} {u : MulAut R}
    (hAut : LargeEvenGraphAut π (fun h h' =>
      (↑h' : Matrix.GeneralLinearGroup ι 𝕂) = A * (↑h : Matrix.GeneralLinearGroup ι 𝕂) * A⁻¹) u)
    (k : ℕ) (h : ↥H) :
    (u ^ k) (π h) = π (kgLangCInnerAux_conjPowElem H A hH k h) := by
  induction k with
  | zero => simp [kgLangCInnerAux_conjPowElem]
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih]
      have h2 := hAut (kgLangCInnerAux_conjPowElem H A hH k h)
        ⟨A * (↑(kgLangCInnerAux_conjPowElem H A hH k h) : Matrix.GeneralLinearGroup ι 𝕂) * A⁻¹,
          hH _⟩ rfl
      rw [h2]
      congr 1
      apply Subtype.ext
      simp only [kgLangCInnerAux_conjPowElem]
      group

theorem kgLangC_conjImage_pow_inner_linear {d : ℕ} (hd : 1 ≤ d) (𝕂 : Type) [Field 𝕂] :
    ∀ u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂)) Set.univ,
      ∃ r : LargeEvenProj (LargeEvenSLGroup (Fin d) 𝕂), u ^ d = MulAut.conj r := by
  intro u hu
  obtain ⟨A, -, hAut⟩ := hu
  have hHmem : ∀ h : ↥(LargeEvenSLGroup (Fin d) 𝕂),
      A * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂) * A⁻¹ ∈ LargeEvenSLGroup (Fin d) 𝕂 := by
    intro h
    have hc : A * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂) * A⁻¹ ∈
        (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin d) 𝕂 →* 𝕂ˣ).ker :=
      (MonoidHom.normal_ker
        (Matrix.GeneralLinearGroup.det :
          Matrix.GeneralLinearGroup (Fin d) 𝕂 →* 𝕂ˣ)).conj_mem h h.2 A
    exact hc
  set M : Matrix.GeneralLinearGroup (Fin d) 𝕂 :=
    Matrix.GeneralLinearGroup.scalar (Fin d) ((Matrix.GeneralLinearGroup.det A)⁻¹) * A ^ d with hMdef
  have hM : M ∈ LargeEvenSLGroup (Fin d) 𝕂 := by
    change M ∈ (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin d) 𝕂 →* 𝕂ˣ).ker
    rw [MonoidHom.mem_ker, hMdef, map_mul, map_pow, Matrix.GeneralLinearGroup.det_scalar,
      Fintype.card_fin, inv_pow]
    group
  have hAd : A ^ d =
      Matrix.GeneralLinearGroup.scalar (Fin d) (Matrix.GeneralLinearGroup.det A) * M := by
    rw [hMdef, ← mul_assoc, ← map_mul]
    simp
  refine ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂) ⟨M, hM⟩, ?_⟩
  ext x
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective x
  rw [← hh]
  change (u ^ d) (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂) h) =
    (MulAut.conj (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂) ⟨M, hM⟩))
      (LargeEvenProjMk (LargeEvenSLGroup (Fin d) 𝕂) h)
  rw [kgLangCInnerAux_pow_apply (LargeEvenSLGroup (Fin d) 𝕂) A hHmem hAut d h]
  have harg : kgLangCInnerAux_conjPowElem (LargeEvenSLGroup (Fin d) 𝕂) A hHmem d h =
      ⟨M, hM⟩ * h * ⟨M, hM⟩⁻¹ := by
    apply Subtype.ext
    have hcentral : Commute
        (Matrix.GeneralLinearGroup.scalar (Fin d) (Matrix.GeneralLinearGroup.det A))
        (M * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂) * M⁻¹) := by
      refine ((TypeA.commute_scalar_GL (Matrix.GeneralLinearGroup.det A) M).mul_right
        (TypeA.commute_scalar_GL (Matrix.GeneralLinearGroup.det A)
          (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂))).mul_right
        (TypeA.commute_scalar_GL (Matrix.GeneralLinearGroup.det A) M).inv_right
    calc A ^ d * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂) * (A ^ d)⁻¹
        = (Matrix.GeneralLinearGroup.scalar (Fin d) (Matrix.GeneralLinearGroup.det A) * M)
            * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂)
            * (Matrix.GeneralLinearGroup.scalar (Fin d)
                (Matrix.GeneralLinearGroup.det A) * M)⁻¹ := by rw [hAd]
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) (Matrix.GeneralLinearGroup.det A)
            * (M * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂) * M⁻¹)
            * (Matrix.GeneralLinearGroup.scalar (Fin d)
                (Matrix.GeneralLinearGroup.det A))⁻¹ := by group
      _ = (M * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂) * M⁻¹)
            * Matrix.GeneralLinearGroup.scalar (Fin d) (Matrix.GeneralLinearGroup.det A)
            * (Matrix.GeneralLinearGroup.scalar (Fin d)
                (Matrix.GeneralLinearGroup.det A))⁻¹ := by rw [hcentral.eq]
      _ = M * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂) * M⁻¹ := by group
  rw [harg, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem kgLangC_conjImage_pow_inner_unitary {d n : ℕ} (hd : 1 ≤ d) (𝕂 : Type) [Field 𝕂] [Finite 𝕂]
    (h𝕂 : Nat.card 𝕂 = (2 ^ n) ^ 2) :
    ∀ u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
        (LargeEvenGUSet (Fin d) 𝕂 (2 ^ n)),
      ∃ r : LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)), u ^ d = MulAut.conj r := by
  intro u hu
  obtain ⟨A, hAGU, hAut⟩ := hu
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h] at h𝕂
      have := Finite.one_lt_card (α := 𝕂)
      norm_num at h𝕂
      omega
    · exact h
  have hfield := unitaryFieldData_of_card hn h𝕂
  haveI : CharP 𝕂 2 := hfield.charP
  let σ : 𝕂 →+* 𝕂 := iterateFrobenius 𝕂 2 n
  have hσ : ∀ x, σ x = x ^ 2 ^ n := iterateFrobenius_def 2 n
  have hm : ∀ M : Matrix (Fin d) (Fin d) 𝕂, M.map (· ^ 2 ^ n) = M.map σ := fun M => by
    ext i j
    simp [hσ]
  have hN : A ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n) : Set (Matrix.GeneralLinearGroup (Fin d) 𝕂)) :=
    TableBUE.gu_subset_normalizer hfield hAGU
  have hHmem : ∀ h : ↥(LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)),
      A * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂) * A⁻¹ ∈
        LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n) := by
    intro h
    exact (Subgroup.mem_normalizer_iff.mp hN ↑h).mp h.2
  have hSU : LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n) = Subgroup.closure (TableB.suGens σ) := by
    unfold LargeEvenSUGroup TableB.suGens
    simp only [hm]
  obtain ⟨μ, hμ0, hμfix, hAμ⟩ := hAGU
  set M : Matrix.GeneralLinearGroup (Fin d) 𝕂 :=
    Matrix.GeneralLinearGroup.scalar (Fin d) ((Matrix.GeneralLinearGroup.det A)⁻¹) * A ^ d
      with hMdef
  have hMmem : M ∈ TableB.suGens σ := by
    refine ⟨?_, ?_⟩
    · have hdetGL : Matrix.GeneralLinearGroup.det M = 1 := by
        rw [hMdef, map_mul, map_pow, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
          inv_pow]
        group
      have := congrArg Units.val hdetGL
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
    · have hAσ : Matrix.transpose ((A : Matrix (Fin d) (Fin d) 𝕂).map σ) *
          (A : Matrix (Fin d) (Fin d) 𝕂) = μ • 1 := by
        rw [← hm]
        exact hAμ
      have hAA : (A : Matrix (Fin d) (Fin d) 𝕂) *
          ((A⁻¹ : Matrix.GeneralLinearGroup (Fin d) 𝕂) :
            Matrix (Fin d) (Fin d) 𝕂) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hAt : Matrix.transpose ((A : Matrix (Fin d) (Fin d) 𝕂).map σ) =
          μ • ((A⁻¹ : Matrix.GeneralLinearGroup (Fin d) 𝕂) :
            Matrix (Fin d) (Fin d) 𝕂) := by
        calc Matrix.transpose ((A : Matrix (Fin d) (Fin d) 𝕂).map σ) =
              Matrix.transpose ((A : Matrix (Fin d) (Fin d) 𝕂).map σ) *
                ((A : Matrix (Fin d) (Fin d) 𝕂) *
                  ((A⁻¹ : Matrix.GeneralLinearGroup (Fin d) 𝕂) :
                    Matrix (Fin d) (Fin d) 𝕂)) := by
              rw [hAA, Matrix.mul_one]
          _ = μ • ((A⁻¹ : Matrix.GeneralLinearGroup (Fin d) 𝕂) :
                Matrix (Fin d) (Fin d) 𝕂) := by
              rw [← Matrix.mul_assoc, hAσ, Matrix.smul_mul, Matrix.one_mul]
      have hAinvpow : (((A⁻¹ : Matrix.GeneralLinearGroup (Fin d) 𝕂)) :
            Matrix (Fin d) (Fin d) 𝕂) ^ d =
          ((((A : Matrix.GeneralLinearGroup (Fin d) 𝕂)) :
            Matrix (Fin d) (Fin d) 𝕂) ^ d)⁻¹ := by
        rw [← Units.val_pow_eq_pow_val, inv_pow, Matrix.GeneralLinearGroup.coe_inv,
          Units.val_pow_eq_pow_val]
      have hcancel : ((((A : Matrix.GeneralLinearGroup (Fin d) 𝕂)) :
            Matrix (Fin d) (Fin d) 𝕂) ^ d)⁻¹ *
          ((A : Matrix.GeneralLinearGroup (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) ^ d = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← Matrix.GeneralLinearGroup.coe_inv,
          ← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hpow : (Matrix.transpose ((A : Matrix (Fin d) (Fin d) 𝕂).map σ)) ^ d *
          (A : Matrix (Fin d) (Fin d) 𝕂) ^ d = μ ^ d • (1 : Matrix (Fin d) (Fin d) 𝕂) := by
        rw [hAt, smul_pow, hAinvpow, Matrix.smul_mul, hcancel]
      have hMmat : (M : Matrix (Fin d) (Fin d) 𝕂) =
          (↑((Matrix.GeneralLinearGroup.det A)⁻¹) : 𝕂) •
            (A : Matrix (Fin d) (Fin d) 𝕂) ^ d := by
        rw [hMdef, TableB.coe_scalar_mul, Units.val_pow_eq_pow_val]
      have hdetrel : (A : Matrix (Fin d) (Fin d) 𝕂).det ^ 2 ^ n *
          (A : Matrix (Fin d) (Fin d) 𝕂).det = μ ^ d := by
        have h1 := congrArg Matrix.det hAσ
        rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
          Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one] at h1
        simpa only [hσ] using h1
      have hscalar : σ (↑((Matrix.GeneralLinearGroup.det A)⁻¹) : 𝕂) *
          (↑((Matrix.GeneralLinearGroup.det A)⁻¹) : 𝕂) * μ ^ d = 1 := by
        have hδ0 : (A : Matrix (Fin d) (Fin d) 𝕂).det ≠ 0 := by
          rw [← Matrix.GeneralLinearGroup.val_det_apply]
          exact Units.ne_zero (Matrix.GeneralLinearGroup.det A)
        have hc : (↑((Matrix.GeneralLinearGroup.det A)⁻¹) : 𝕂) =
            ((A : Matrix (Fin d) (Fin d) 𝕂).det)⁻¹ := by
          rw [Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply]
        have hσc : σ (↑((Matrix.GeneralLinearGroup.det A)⁻¹) : 𝕂) =
            (((A : Matrix (Fin d) (Fin d) 𝕂).det) ^ 2 ^ n)⁻¹ := by
          rw [hc, map_inv₀ σ, hσ]
        rw [hσc, hc, ← hdetrel, ← _root_.mul_inv_rev]
        have hcomm : (A : Matrix (Fin d) (Fin d) 𝕂).det *
            (A : Matrix (Fin d) (Fin d) 𝕂).det ^ 2 ^ n =
            (A : Matrix (Fin d) (Fin d) 𝕂).det ^ 2 ^ n *
            (A : Matrix (Fin d) (Fin d) 𝕂).det := by
          rw [← pow_succ', ← pow_succ, add_comm]
        rw [← hcomm]
        exact inv_mul_cancel₀ (mul_ne_zero hδ0 (pow_ne_zero _ hδ0))
      rw [hMmat, TableB.transpose_map_smul, Matrix.map_pow, Matrix.transpose_pow,
        Matrix.smul_mul, Matrix.mul_smul]
      rw [hpow, smul_smul, smul_smul, hscalar, one_smul]
  have hM : M ∈ LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n) := by
    rw [hSU]
    exact Subgroup.subset_closure hMmem
  have hAd : A ^ d =
      Matrix.GeneralLinearGroup.scalar (Fin d) (Matrix.GeneralLinearGroup.det A) * M := by
    rw [hMdef, ← mul_assoc, ← map_mul]
    simp
  refine ⟨LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)) ⟨M, hM⟩, ?_⟩
  ext x
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective x
  rw [← hh]
  change (u ^ d) (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)) h) =
    (MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)) ⟨M, hM⟩))
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)) h)
  rw [kgLangCInnerAux_pow_apply (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)) A hHmem hAut d h]
  have harg : kgLangCInnerAux_conjPowElem (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)) A hHmem d h =
      ⟨M, hM⟩ * h * ⟨M, hM⟩⁻¹ := by
    apply Subtype.ext
    have hcentral : Commute
        (Matrix.GeneralLinearGroup.scalar (Fin d) (Matrix.GeneralLinearGroup.det A))
        (M * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂) * M⁻¹) := by
      refine ((TypeA.commute_scalar_GL (Matrix.GeneralLinearGroup.det A) M).mul_right
        (TypeA.commute_scalar_GL (Matrix.GeneralLinearGroup.det A)
          (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂))).mul_right
        (TypeA.commute_scalar_GL (Matrix.GeneralLinearGroup.det A) M).inv_right
    calc A ^ d * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂) * (A ^ d)⁻¹
        = (Matrix.GeneralLinearGroup.scalar (Fin d) (Matrix.GeneralLinearGroup.det A) * M)
            * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂)
            * (Matrix.GeneralLinearGroup.scalar (Fin d)
                (Matrix.GeneralLinearGroup.det A) * M)⁻¹ := by rw [hAd]
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) (Matrix.GeneralLinearGroup.det A)
            * (M * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂) * M⁻¹)
            * (Matrix.GeneralLinearGroup.scalar (Fin d)
                (Matrix.GeneralLinearGroup.det A))⁻¹ := by group
      _ = (M * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂) * M⁻¹)
            * Matrix.GeneralLinearGroup.scalar (Fin d) (Matrix.GeneralLinearGroup.det A)
            * (Matrix.GeneralLinearGroup.scalar (Fin d)
                (Matrix.GeneralLinearGroup.det A))⁻¹ := by rw [hcentral.eq]
      _ = M * (↑h : Matrix.GeneralLinearGroup (Fin d) 𝕂) * M⁻¹ := by group
  rw [harg, MulAut.conj_apply, map_mul, map_mul, map_inv]

end CFSG.StandardType
