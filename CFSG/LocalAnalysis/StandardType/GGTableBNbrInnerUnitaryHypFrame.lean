module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypEigen
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypTorus

public section

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  TableB

variable {n r p : ℕ} {K : Type} [Field K]

theorem gram_submatrix_conj (h : UnitaryFieldData 2 n K)
    (N : Matrix (HypIndex r 0) (HypIndex r 0) K) (e : HypIndex r 0 ≃ HypIndex r 0) :
    (((N.submatrix id e).map h.bar)ᵀ * hypGram r 0 K) * N.submatrix id e =
      (((N.map h.bar)ᵀ * hypGram r 0 K) * N).submatrix e e := by
  ext a b
  simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]

theorem gram_conjTranspose (h : UnitaryFieldData 2 n K)
    (N : Matrix (HypIndex r 0) (HypIndex r 0) K) :
    ((((N.map h.bar)ᵀ * hypGram r 0 K) * N).map h.bar)ᵀ =
      ((N.map h.bar)ᵀ * hypGram r 0 K) * N := by
  have hbb : (⇑h.bar ∘ ⇑h.bar) = id := funext fun c => h.bar_bar c
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    hypGram_conjTranspose, Matrix.transpose_map, Matrix.map_map, hbb, Matrix.map_id]
  simp only [Matrix.transpose_transpose, Matrix.mul_assoc]

theorem gram_bar_symm (h : UnitaryFieldData 2 n K)
    (N : Matrix (HypIndex r 0) (HypIndex r 0) K) (i j : HypIndex r 0) :
    h.bar ((((N.map h.bar)ᵀ * hypGram r 0 K) * N) i j) =
      (((N.map h.bar)ᵀ * hypGram r 0 K) * N) j i := by
  have := congrFun (congrFun (gram_conjTranspose h N) j) i
  simpa only [Matrix.transpose_apply, Matrix.map_apply] using this

theorem conj_diagonal_gram_apply (h : UnitaryFieldData 2 n K)
    (A : Matrix (HypIndex r 0) (HypIndex r 0) K) (lam : HypIndex r 0 → Kˣ)
    (a b : HypIndex r 0) :
    (((A * diagonal (fun a => ((lam a : Kˣ) : K))).map h.bar)ᵀ * hypGram r 0 K *
        (A * diagonal (fun a => ((lam a : Kˣ) : K)))) a b =
      h.bar (lam a) * (lam b : K) * (((A.map h.bar)ᵀ * hypGram r 0 K) * A) a b := by
  have hassoc :
      (diagonal (fun a => h.bar ((lam a : Kˣ) : K)) * (A.map h.bar)ᵀ) * hypGram r 0 K *
          (A * diagonal (fun a => ((lam a : Kˣ) : K))) =
        diagonal (fun a => h.bar ((lam a : Kˣ) : K)) *
          (((A.map h.bar)ᵀ * hypGram r 0 K) * A) *
          diagonal (fun a => ((lam a : Kˣ) : K)) := by
    simp only [Matrix.mul_assoc]
  rw [Matrix.map_mul, Matrix.diagonal_map (map_zero h.bar), Matrix.transpose_mul,
    Matrix.diagonal_transpose, hassoc]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

theorem exists_hyperbolic_frame_matrix (h : UnitaryFieldData 2 n K) (N : GL (HypIndex r 0) K)
    (τ : Equiv.Perm (HypIndex r 0)) (e : HypIndex r 0 ≃ HypIndex r 0)
    (he : ∀ a, e (hypPartner a) = τ (e a))
    (hmono : ∀ i j,
      ((((N : Matrix (HypIndex r 0) (HypIndex r 0) K).map h.bar)ᵀ * hypGram r 0 K) *
        (N : Matrix (HypIndex r 0) (HypIndex r 0) K)) i j ≠ 0 → j = τ i)
    (hne : ∀ i,
      ((((N : Matrix (HypIndex r 0) (HypIndex r 0) K).map h.bar)ᵀ * hypGram r 0 K) *
        (N : Matrix (HypIndex r 0) (HypIndex r 0) K)) i (τ i) ≠ 0) :
    ∃ (M : GL (HypIndex r 0) K) (lam : HypIndex r 0 → Kˣ),
      (M : Matrix (HypIndex r 0) (HypIndex r 0) K) =
        (N : Matrix (HypIndex r 0) (HypIndex r 0) K).submatrix id e *
          diagonal (fun a => ((lam a : Kˣ) : K)) ∧
      ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).map h.bar)ᵀ * hypGram r 0 K *
        (M : Matrix (HypIndex r 0) (HypIndex r 0) K) = hypGram r 0 K := by
  classical
  let G : Matrix (HypIndex r 0) (HypIndex r 0) K :=
    ((N : Matrix (HypIndex r 0) (HypIndex r 0) K).map h.bar)ᵀ * hypGram r 0 K *
      (N : Matrix (HypIndex r 0) (HypIndex r 0) K)
  have hmono' : ∀ i j, G i j ≠ 0 → j = τ i := hmono
  have hne' : ∀ i, G i (τ i) ≠ 0 := hne
  have hGne : ∀ i, G (e (.inl i)) (e (.inr (.inr i))) ≠ 0 := by
    intro i
    have hτ : e (.inr (.inr i)) = τ (e (.inl i)) := by simpa using he (.inl i)
    rw [hτ]
    exact hne' (e (.inl i))
  let lam : HypIndex r 0 → Kˣ := fun a =>
    match a with
    | .inl _ => 1
    | .inr (.inl k) => k.elim0
    | .inr (.inr i) => Units.mk0 (G (e (.inl i)) (e (.inr (.inr i))))⁻¹ (inv_ne_zero (hGne i))
  let Mmat : Matrix (HypIndex r 0) (HypIndex r 0) K :=
    (N : Matrix (HypIndex r 0) (HypIndex r 0) K).submatrix id e *
      diagonal (fun a => ((lam a : Kˣ) : K))
  have hconj : ((Mmat.map h.bar)ᵀ * hypGram r 0 K) * Mmat = hypGram r 0 K := by
    ext a b
    rw [hypGram_apply]
    change ((((N : Matrix (HypIndex r 0) (HypIndex r 0) K).submatrix id e *
      diagonal (fun a => ((lam a : Kˣ) : K))).map h.bar)ᵀ * hypGram r 0 K *
      ((N : Matrix (HypIndex r 0) (HypIndex r 0) K).submatrix id e *
        diagonal (fun a => ((lam a : Kˣ) : K)))) a b = _
    rw [conj_diagonal_gram_apply h
      ((N : Matrix (HypIndex r 0) (HypIndex r 0) K).submatrix id e) lam a b]
    rw [gram_submatrix_conj h (N : Matrix (HypIndex r 0) (HypIndex r 0) K) e]
    simp only [Matrix.submatrix_apply]
    change h.bar (lam a) * (lam b : K) * G (e a) (e b) = _
    by_cases hb : b = hypPartner a
    · rw [if_pos hb, hb]
      rcases a with i | k | i
      · simp only [hypPartner_inl, lam, Units.val_one, map_one, one_mul]
        rw [Units.val_mk0, inv_mul_cancel₀ (hGne i)]
      · exact k.elim0
      · simp only [hypPartner_inr_inr, lam, Units.val_one, mul_one, Units.val_mk0, map_inv₀]
        have hsym : h.bar (G (e (.inl i)) (e (.inr (.inr i)))) =
            G (e (.inr (.inr i))) (e (.inl i)) :=
          gram_bar_symm h (N : Matrix (HypIndex r 0) (HypIndex r 0) K)
            (e (.inl i)) (e (.inr (.inr i)))
        rw [← hsym, inv_mul_cancel₀]
        exact fun h0 => hGne i ((h.bar_eq_zero_iff).mp h0)
    · rw [if_neg hb]
      have hzero : G (e a) (e b) = 0 := by
        by_contra hne0
        have := hmono' (e a) (e b) hne0
        rw [← he a] at this
        exact hb (e.injective this)
      rw [hzero, mul_zero]
  have hdetMmat : Mmat.det ≠ 0 := by
    change ((N : Matrix (HypIndex r 0) (HypIndex r 0) K).submatrix id e *
      diagonal (fun a => ((lam a : Kˣ) : K))).det ≠ 0
    rw [Matrix.det_mul]
    refine mul_ne_zero ?_ ?_
    · rw [Matrix.det_permute']
      refine mul_ne_zero ?_
        (Matrix.isUnits_det_units (N : (Matrix (HypIndex r 0) (HypIndex r 0) K)ˣ)).ne_zero
      rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]
    · rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun a _ => Units.ne_zero (lam a)
  refine ⟨GeneralLinearGroup.mkOfDetNeZero Mmat hdetMmat, lam, ?_, ?_⟩
  · rfl
  · exact hconj

theorem exists_mem_hypSU_of_isometry (h : UnitaryFieldData 2 n K) (hr : 0 < r)
    (M : GL (HypIndex r 0) K)
    (hM : ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).map h.bar)ᵀ * hypGram r 0 K *
      (M : Matrix (HypIndex r 0) (HypIndex r 0) K) = hypGram r 0 K) :
    ∃ (g : hypSU h r 0) (a : Fin r → Kˣ),
      (((g : hypSU h r 0) : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) =
        (M : Matrix (HypIndex r 0) (HypIndex r 0) K) *
          diagonal (torusEntries h a (Fin.elim0 : Fin 0 → Kˣ)) := by
  classical
  have hdetJ : h.bar ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).det) *
      (hypGram r 0 K).det * ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).det) =
      (hypGram r 0 K).det := by
    have hmap : ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).map h.bar).det =
        h.bar ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).det) :=
      (RingHom.map_det h.bar (M : Matrix (HypIndex r 0) (HypIndex r 0) K)).symm
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmap] at h
    simpa only [mul_assoc] using h
  have h5 : h.bar ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).det) *
      ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).det) = 1 := by
    have h4 : (hypGram r 0 K).det *
        (h.bar ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).det) *
          ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).det)) = (hypGram r 0 K).det * 1 := by
      rw [mul_one, ← mul_assoc,
        mul_comm (hypGram r 0 K).det (h.bar ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).det)),
        hdetJ]
    exact mul_left_cancel₀ det_hypGram_ne_zero h4
  have hnorm : h.norm ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).det) = 1 := by
    show ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).det) *
      h.bar ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).det) = 1
    rw [mul_comm, h5]
  obtain ⟨c, hc0, hc⟩ := h.exists_div_bar_eq hnorm
  let i0 : Fin r := ⟨0, hr⟩
  let a : Fin r → Kˣ := Function.update (fun _ => 1) i0 (Units.mk0 c⁻¹ (inv_ne_zero hc0))
  let D : Matrix (HypIndex r 0) (HypIndex r 0) K :=
    diagonal (torusEntries h a (Fin.elim0 : Fin 0 → Kˣ))
  have hratio : torusRatio h a (Fin.elim0 : Fin 0 → Kˣ) =
      ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).det)⁻¹ := by
    rw [torusRatio]
    have h0 : (∏ k : Fin 0, ((Fin.elim0 k : Kˣ) : K)) = 1 := by simp
    rw [h0, mul_one]
    have hf : (∏ i, ((a i : K) / h.bar (a i))) = c⁻¹ / h.bar (c⁻¹) := by
      rw [Fintype.prod_eq_single i0]
      · simp only [a, Function.update_self, Units.val_mk0]
      · intro j hj
        simp [a, Function.update_of_ne hj]
    rw [hf]
    have hkey : c⁻¹ / h.bar (c⁻¹) = (c / h.bar c)⁻¹ := by
      rw [map_inv₀, div_inv_eq_mul, inv_div, div_eq_mul_inv, mul_comm]
    rw [hkey, hc]
  have hdetD : D.det = ((M : Matrix (HypIndex r 0) (HypIndex r 0) K).det)⁻¹ := by
    rw [det_diagonal_torusEntries, hratio]
  have hMD_iso : (((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D).map h.bar)ᵀ *
      hypGram r 0 K * ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D) = hypGram r 0 K := by
    rw [conjTranspose_mul_mul, hM]
    exact diagonal_torusEntries_isometry h a (d := (Fin.elim0 : Fin 0 → Kˣ)) (fun k => k.elim0)
  have hdetMD : (((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D).det) = 1 := by
    rw [Matrix.det_mul, hdetD, mul_inv_cancel₀ (Matrix.isUnits_det_units M).ne_zero]
  refine ⟨⟨GeneralLinearGroup.mkOfDetNeZero
    ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D) ?_, ?_⟩, a, ?_⟩
  · rw [hdetMD]; exact one_ne_zero
  · exact mem_hypSU.mpr ⟨hMD_iso, hdetMD⟩
  · rfl

theorem exists_chi_pow {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) {u : Kˣ}
    (hu : u ^ p = 1) : ∃ t : ZMod p, (u : K) = ζ ^ t.val := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have huK : (u : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  obtain ⟨j, hj, hje⟩ := hζ.eq_pow_of_pow_eq_one huK
  exact ⟨(j : ZMod p), by rw [ZMod.val_natCast_of_lt hj]; exact hje.symm⟩

theorem diagonal_mul_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (d₁ d₂ : ι → K) :
    diagonal d₁ * diagonal d₂ = diagonal d₂ * diagonal d₁ := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem eigen_submatrix_conj {h : UnitaryFieldData 2 n K} {p : ℕ}
    {E : Subgroup (hypSU h r 0)} (F : HypEigenframe h p E)
    (e : HypIndex r 0 ≃ HypIndex r 0) (x : E) :
    (((x : hypSU h r 0) : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) *
        (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K).submatrix id e =
      (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K).submatrix id e *
        diagonal (fun a => ((F.χ x (e a) : Kˣ) : K)) := by
  ext a b
  have hL : (∑ c, (((x : hypSU h r 0) : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) a c *
      (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K).submatrix id e c b) =
      (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K) a (e b) *
        ((F.χ x (e b) : Kˣ) : K) := by
    calc (∑ c, (((x : hypSU h r 0) : GL (HypIndex r 0) K) :
            Matrix (HypIndex r 0) (HypIndex r 0) K) a c *
          (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K).submatrix id e c b)
        = ((((x : hypSU h r 0) : GL (HypIndex r 0) K) :
            Matrix (HypIndex r 0) (HypIndex r 0) K) *
            (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K)) a (e b) := by
          rw [Matrix.mul_apply]; simp [Matrix.submatrix_apply]
      _ = ((F.N : Matrix (HypIndex r 0) (HypIndex r 0) K) *
            diagonal (fun i => ((F.χ x i : Kˣ) : K))) a (e b) := by rw [F.conj x]
      _ = (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K) a (e b) *
            ((F.χ x (e b) : Kˣ) : K) := by
          rw [Matrix.mul_apply,
            Fintype.sum_eq_single (e b) (fun c hc => by
              rw [Matrix.diagonal_apply_ne _ hc, mul_zero])]
          simp
  have hR : ((F.N : Matrix (HypIndex r 0) (HypIndex r 0) K).submatrix id e *
        diagonal (fun a => ((F.χ x (e a) : Kˣ) : K))) a b =
      (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K) a (e b) *
        ((F.χ x (e b) : Kˣ) : K) := by
    rw [Matrix.mul_apply,
      Fintype.sum_eq_single b (fun c hc => by
        rw [Matrix.diagonal_apply_ne _ hc, mul_zero])]
    simp [Matrix.submatrix_apply]
  rw [Matrix.mul_apply, hL, hR]

theorem exists_conj_hypEntries (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hr : 0 < r)
    (E : Subgroup (hypSU h r 0)) (hE : IsElemAbelian p E) (hcard : p ^ r ≤ Nat.card E) :
    ∃ g : hypSU h r 0, ∀ x ∈ E, ∃ t : Fin r → ZMod p,
      ((((g * x * g⁻¹ : hypSU h r 0) : GL (HypIndex r 0) K)) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) = diagonal (hypEntries ζ t) := by
  classical
  obtain ⟨F⟩ := nonempty_hypEigenframe h hp hpq E hE
  obtain ⟨τ, hτ1, hτ2, hmono, hne⟩ := F.exists_gram_monomial hp hp2 hpq hcard
  have hcardHyp : Fintype.card (HypIndex r 0) = 2 * r := by
    simp [HypIndex, Fintype.card_sum, two_mul]
  obtain ⟨e, he⟩ := exists_equiv_hypIndex_of_fpf_involution hcardHyp τ hτ1 hτ2
  obtain ⟨M, lam, hMmat, hMiso⟩ := exists_hyperbolic_frame_matrix h F.N τ e he hmono hne
  obtain ⟨g₀, a, hg₀⟩ := exists_mem_hypSU_of_isometry h hr M hMiso
  refine ⟨g₀⁻¹, ?_⟩
  intro x hxE
  rw [inv_inv]
  let xE : E := ⟨x, hxE⟩
  let A : Matrix (HypIndex r 0) (HypIndex r 0) K :=
    (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K).submatrix id e
  let Dlam : Matrix (HypIndex r 0) (HypIndex r 0) K := diagonal (fun i => ((lam i : Kˣ) : K))
  let D : Matrix (HypIndex r 0) (HypIndex r 0) K :=
    diagonal (torusEntries h a (Fin.elim0 : Fin 0 → Kˣ))
  let xMat : Matrix (HypIndex r 0) (HypIndex r 0) K :=
    ((x : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K)
  let diagχ : Matrix (HypIndex r 0) (HypIndex r 0) K :=
    diagonal (fun i => ((F.χ xE (e i) : Kˣ) : K))
  have hM : (M : Matrix (HypIndex r 0) (HypIndex r 0) K) = A * Dlam := hMmat
  have hcomm1 : diagχ * Dlam = Dlam * diagχ := by
    simp only [diagχ, Dlam]
    exact diagonal_mul_comm _ _
  have hcomm2 : diagχ * D = D * diagχ := by
    simp only [diagχ, D]
    exact diagonal_mul_comm _ _
  have hxM : xMat * (M : Matrix (HypIndex r 0) (HypIndex r 0) K) =
      (M : Matrix (HypIndex r 0) (HypIndex r 0) K) * diagχ := by
    rw [hM]
    calc xMat * (A * Dlam)
        = (xMat * A) * Dlam := by rw [Matrix.mul_assoc]
      _ = (A * diagχ) * Dlam := by rw [eigen_submatrix_conj F e xE]
      _ = A * (diagχ * Dlam) := by rw [Matrix.mul_assoc]
      _ = A * (Dlam * diagχ) := by rw [hcomm1]
      _ = (A * Dlam) * diagχ := by rw [← Matrix.mul_assoc]
  have hxM' : xMat * ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D) =
      ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D) * diagχ := by
    rw [← Matrix.mul_assoc, hxM, Matrix.mul_assoc, hcomm2, ← Matrix.mul_assoc]
  have hM'M' : ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D)⁻¹ *
      ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D) = 1 := by
    rw [← hg₀, ← GeneralLinearGroup.coe_inv, ← GeneralLinearGroup.coe_mul, inv_mul_cancel,
      GeneralLinearGroup.coe_one]
  have hconj_diag : ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D)⁻¹ * xMat *
      ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D) = diagχ := by
    calc ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D)⁻¹ * xMat *
          ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D)
        = ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D)⁻¹ *
            (xMat * ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D)) := by
          rw [Matrix.mul_assoc]
      _ = ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D)⁻¹ *
            (((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D) * diagχ) := by rw [hxM']
      _ = (((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D)⁻¹ *
            ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D)) * diagχ := by
          rw [← Matrix.mul_assoc]
      _ = 1 * diagχ := by rw [hM'M']
      _ = diagχ := by rw [Matrix.one_mul]
  choose t ht using fun i => exists_chi_pow (hζ := hζ) hp (F.pow xE (e (.inl i)))
  refine ⟨t, ?_⟩
  have hdiag : diagχ = diagonal (hypEntries ζ t) := by
    change diagonal (fun i => ((F.χ xE (e i) : Kˣ) : K)) = diagonal (hypEntries ζ t)
    rw [Matrix.diagonal_eq_diagonal_iff]
    intro i
    rcases i with j | k | j
    · simpa [hypEntries] using ht j
    · exact k.elim0
    · have hg : e (.inr (.inr j)) = τ (e (.inl j)) := by simpa using he (.inl j)
      have hτinv : (F.χ xE (e (.inr (.inr j))) : K) = ((F.χ xE (e (.inl j)) : K))⁻¹ := by
        have h1 : F.χ xE (e (.inr (.inr j))) = (F.χ xE (e (.inl j)))⁻¹ := by
          rw [hg]
          exact eq_inv_of_mul_eq_one_right (F.chi_mul_chi_eq_one hpq (hne (e (.inl j))) xE)
        rw [h1, Units.val_inv_eq_inv_val]
      rw [hτinv, ht j]
      rfl
  have hgl : (((g₀⁻¹ * x * g₀ : hypSU h r 0) : GL (HypIndex r 0) K) :
      Matrix (HypIndex r 0) (HypIndex r 0) K) =
      ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D)⁻¹ * xMat *
        ((M : Matrix (HypIndex r 0) (HypIndex r 0) K) * D) := by
    change ((((g₀ : GL (HypIndex r 0) K)⁻¹ : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) * xMat *
      ((g₀ : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K)) = _
    rw [GeneralLinearGroup.coe_inv, hg₀]
  rw [hgl, hconj_diag, hdiag]

end CFSG.StandardType

end
