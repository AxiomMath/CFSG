module

public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitC
public import CFSG.ClassicalGroups.UnitaryFlag.WittBasis
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrderSupport
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

section WittTransitivity

open CFSG.Open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  Matrix CFSG.LinearGroups

private theorem ggKGUf_ker_separating {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (v : HypIndex r 1 → K) (hv : hypForm h r 1 v v = 1) :
    ((hypForm h r 1).domRestrict₁₂ (LinearMap.ker (hypForm h r 1 v))
      (LinearMap.ker (hypForm h r 1 v))).SeparatingLeft ∧
    Module.finrank K (LinearMap.ker (hypForm h r 1 v)) + 1 =
      Module.finrank K (HypIndex r 1 → K) :=
  separatingLeft_ker_of_norm_one h (hypForm_isSymm h) (hypForm_separatingLeft h) hv

private theorem ggKGUf_perp_basis {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (v : HypIndex r 1 → K) (hv : hypForm h r 1 v v = 1) :
    ∃ w : Module.Basis (HypIndex r 0) K (LinearMap.ker (hypForm h r 1 v)),
      ∀ x y, hypForm h r 1 ((w x : LinearMap.ker (hypForm h r 1 v)) : HypIndex r 1 → K)
        ((w y : LinearMap.ker (hypForm h r 1 v)) : HypIndex r 1 → K) = hypGram r 0 K x y := by
  obtain ⟨hsep, hdim⟩ := ggKGUf_ker_separating h v hv
  have hfin : Module.finrank K (HypIndex r 1 → K) = 2 * r + 1 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [HypIndex, Fintype.card_sum]
    omega
  have hdim2 : Module.finrank K (LinearMap.ker (hypForm h r 1 v)) = 2 * r := by omega
  obtain ⟨w, hw⟩ := exists_hypBasis h
    ((hypForm_isSymm h).domRestrict (LinearMap.ker (hypForm h r 1 v))) hsep (r := r) (ε := 0)
    (by omega)
  exact ⟨w, fun x y => by simpa [LinearMap.domRestrict₁₂_apply] using hw x y⟩

private theorem ggKGUf_exists_frame {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (v : HypIndex r 1 → K) (hv : hypForm h r 1 v v = 1) :
    ∃ N : GL (HypIndex r 1) K,
      ((N : Matrix (HypIndex r 1) (HypIndex r 1) K).map h.bar)ᵀ * hypGram r 1 K *
        (N : Matrix (HypIndex r 1) (HypIndex r 1) K) = hypGram r 1 K ∧
      (N : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ
        (Pi.single (Sum.inr (Sum.inl 0)) 1 : HypIndex r 1 → K) = v := by
  classical
  obtain ⟨w, hw⟩ := ggKGUf_perp_basis h v hv
  let col : HypIndex r 1 → HypIndex r 1 → K := fun b =>
    match b with
    | .inl i => ((w (.inl i) : LinearMap.ker (hypForm h r 1 v)) : HypIndex r 1 → K)
    | .inr (.inl _) => v
    | .inr (.inr i) => ((w (.inr (.inr i)) : LinearMap.ker (hypForm h r 1 v)) : HypIndex r 1 → K)
  let Nmat : Matrix (HypIndex r 1) (HypIndex r 1) K := fun a b => col b a
  have hcolvec : ∀ a, Nmat *ᵥ (Pi.single a 1 : HypIndex r 1 → K) = col a := by
    intro a
    rw [Matrix.mulVec_single_one]
    rfl
  have hNv : Nmat *ᵥ (Pi.single (Sum.inr (Sum.inl 0)) 1 : HypIndex r 1 → K) = v := by
    rw [hcolvec]
  have hcol : ∀ a b, hypForm h r 1 (col a) (col b) = hypGram r 1 K a b := by
    intro a b
    have hwv : ∀ x : HypIndex r 0,
        hypForm h r 1 v ((w x : LinearMap.ker (hypForm h r 1 v)) : HypIndex r 1 → K) = 0 :=
      fun x => LinearMap.mem_ker.mp (w x).2
    rcases a with i | k | i <;> rcases b with j | l | j
    ·
      rw [show col (.inl i) = ((w (.inl i) : _) : HypIndex r 1 → K) from rfl,
        show col (.inl j) = ((w (.inl j) : _) : HypIndex r 1 → K) from rfl,
        hw (.inl i) (.inl j)]
      simp [hypGram_inl_inl]
    ·
      rw [show col (.inl i) = ((w (.inl i) : _) : HypIndex r 1 → K) from rfl,
        show col (.inr (.inl l)) = v from rfl]
      rw [← (hypForm_isSymm h).eq v ((w (.inl i) : _) : HypIndex r 1 → K), hwv (.inl i),
        map_zero]
      simp [hypGram_inl_inr_inl]
    ·
      rw [show col (.inl i) = ((w (.inl i) : _) : HypIndex r 1 → K) from rfl,
        show col (.inr (.inr j)) = ((w (.inr (.inr j)) : _) : HypIndex r 1 → K) from rfl,
        hw (.inl i) (.inr (.inr j))]
      simp [hypGram_inl_inr_inr]
    ·
      rw [show col (.inr (.inl k)) = v from rfl,
        show col (.inl j) = ((w (.inl j) : _) : HypIndex r 1 → K) from rfl]
      rw [hwv (.inl j)]
      simp [hypGram_inr_inl_inl]
    ·
      simp only [col]
      rw [hv]
      simp [hypGram_apply, Subsingleton.elim k l]
    ·
      rw [show col (.inr (.inl k)) = v from rfl,
        show col (.inr (.inr j)) = ((w (.inr (.inr j)) : _) : HypIndex r 1 → K) from rfl]
      rw [hwv (.inr (.inr j))]
      simp [hypGram_inr_inl_inr_inr]
    ·
      rw [show col (.inr (.inr i)) = ((w (.inr (.inr i)) : _) : HypIndex r 1 → K) from rfl,
        show col (.inl j) = ((w (.inl j) : _) : HypIndex r 1 → K) from rfl,
        hw (.inr (.inr i)) (.inl j)]
      simp [hypGram_inr_inr_inl]
    ·
      rw [show col (.inr (.inr i)) = ((w (.inr (.inr i)) : _) : HypIndex r 1 → K) from rfl,
        show col (.inr (.inl l)) = v from rfl]
      rw [← (hypForm_isSymm h).eq v ((w (.inr (.inr i)) : _) : HypIndex r 1 → K),
        hwv (.inr (.inr i)), map_zero]
      simp [hypGram_inr_inr_inr_inl]
    ·
      rw [show col (.inr (.inr i)) = ((w (.inr (.inr i)) : _) : HypIndex r 1 → K) from rfl,
        show col (.inr (.inr j)) = ((w (.inr (.inr j)) : _) : HypIndex r 1 → K) from rfl,
        hw (.inr (.inr i)) (.inr (.inr j))]
      simp [hypGram_inr_inr_inr_inr]
  have hiso : (Nmat.map h.bar)ᵀ * hypGram r 1 K * Nmat = hypGram r 1 K := by
    ext a b
    rw [← gramForm_single h ((Nmat.map h.bar)ᵀ * hypGram r 1 K * Nmat) a b,
      ← gramForm_mulVec h (hypGram r 1 K) Nmat (Pi.single a 1) (Pi.single b 1)]
    rw [hcolvec a, hcolvec b]
    exact hcol a b
  have hdetJ : h.bar Nmat.det * (hypGram r 1 K).det * Nmat.det = (hypGram r 1 K).det := by
    have hmap : (Nmat.map h.bar).det = h.bar Nmat.det := (RingHom.map_det h.bar Nmat).symm
    have h := congrArg Matrix.det hiso
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmap] at h
    simpa only [mul_assoc] using h
  have h5 : h.bar Nmat.det * Nmat.det = 1 := by
    have h4 : (hypGram r 1 K).det * (h.bar Nmat.det * Nmat.det) = (hypGram r 1 K).det * 1 := by
      rw [mul_one, ← mul_assoc,
        mul_comm (hypGram r 1 K).det (h.bar Nmat.det), hdetJ]
    exact mul_left_cancel₀ det_hypGram_ne_zero h4
  have hdetN : Nmat.det ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at h5
    exact zero_ne_one h5
  refine ⟨GeneralLinearGroup.mkOfDetNeZero Nmat hdetN, ?_, ?_⟩
  · show (Nmat.map h.bar)ᵀ * hypGram r 1 K * Nmat = hypGram r 1 K
    exact hiso
  · show Nmat *ᵥ (Pi.single (Sum.inr (Sum.inl 0)) 1 : HypIndex r 1 → K) = v
    exact hNv

private theorem ggKGUf_torus_left {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hr : 0 < r) (M : GL (HypIndex r 1) K)
    (hM : ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).map h.bar)ᵀ * hypGram r 1 K *
      (M : Matrix (HypIndex r 1) (HypIndex r 1) K) = hypGram r 1 K) :
    ∃ (g : hypSU h r 1) (a : Fin r → Kˣ),
      ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
        diagonal (torusEntries h a (fun _ : Fin 1 => 1)) *
          (M : Matrix (HypIndex r 1) (HypIndex r 1) K) := by
  classical
  have hdetJ : h.bar ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).det) *
      (hypGram r 1 K).det * ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).det) =
      (hypGram r 1 K).det := by
    have hmap : ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).map h.bar).det =
        h.bar ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).det) :=
      (RingHom.map_det h.bar (M : Matrix (HypIndex r 1) (HypIndex r 1) K)).symm
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmap] at h
    simpa only [mul_assoc] using h
  have h5 : h.bar ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).det) *
      ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).det) = 1 := by
    have h4 : (hypGram r 1 K).det *
        (h.bar ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).det) *
          ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).det)) = (hypGram r 1 K).det * 1 := by
      rw [mul_one, ← mul_assoc,
        mul_comm (hypGram r 1 K).det (h.bar ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).det)),
        hdetJ]
    exact mul_left_cancel₀ det_hypGram_ne_zero h4
  have hnorm : h.norm ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).det) = 1 := by
    show ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).det) *
      h.bar ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).det) = 1
    rw [mul_comm, h5]
  obtain ⟨c, hc0, hc⟩ := h.exists_div_bar_eq hnorm
  let i0 : Fin r := ⟨0, hr⟩
  let a : Fin r → Kˣ := Function.update (fun _ => 1) i0 (Units.mk0 c⁻¹ (inv_ne_zero hc0))
  let D : Matrix (HypIndex r 1) (HypIndex r 1) K :=
    diagonal (torusEntries h a (fun _ : Fin 1 => 1))
  have hratio : torusRatio h a (fun _ : Fin 1 => 1) =
      ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).det)⁻¹ := by
    rw [torusRatio]
    have h0 : (∏ k : Fin 1, (((fun _ : Fin 1 => 1) k : Kˣ) : K)) = 1 := by simp
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
  have hdetD : D.det = ((M : Matrix (HypIndex r 1) (HypIndex r 1) K).det)⁻¹ := by
    rw [det_diagonal_torusEntries, hratio]
  have hDiso : (D.map h.bar)ᵀ * hypGram r 1 K * D = hypGram r 1 K :=
    diagonal_torusEntries_isometry h a (d := fun _ : Fin 1 => 1)
      (fun k => by simp [UnitaryFieldData.norm])
  have hMDiso : ((D * (M : Matrix (HypIndex r 1) (HypIndex r 1) K)).map h.bar)ᵀ *
      hypGram r 1 K * (D * (M : Matrix (HypIndex r 1) (HypIndex r 1) K)) = hypGram r 1 K := by
    rw [conjTranspose_mul_mul h (hypGram r 1 K) D
      (M : Matrix (HypIndex r 1) (HypIndex r 1) K), hDiso, hM]
  have hdetDM : (D * (M : Matrix (HypIndex r 1) (HypIndex r 1) K)).det = 1 := by
    rw [Matrix.det_mul, hdetD, inv_mul_cancel₀ (Matrix.isUnits_det_units M).ne_zero]
  refine ⟨⟨GeneralLinearGroup.mkOfDetNeZero (D * (M : Matrix (HypIndex r 1) (HypIndex r 1) K))
    (by rw [hdetDM]; exact one_ne_zero), mem_hypSU.mpr ⟨hMDiso, hdetDM⟩⟩, a, ?_⟩
  rfl

private theorem ggKGUsOdd_exists_isometry_mid {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hr : 0 < r) (v : HypIndex r 1 → K) (hv : hypForm h r 1 v v = 1) :
    ∃ g : hypSU h r 1, g • v = (Pi.single (Sum.inr (Sum.inl 0)) 1 : HypIndex r 1 → K) := by
  classical
  obtain ⟨N, hNiso, hNv⟩ := ggKGUf_exists_frame h v hv
  have hMN : ((N⁻¹ : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) *
      (N : Matrix (HypIndex r 1) (HypIndex r 1) K) = 1 := by
    rw [← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one]
  have hNM : (N : Matrix (HypIndex r 1) (HypIndex r 1) K) *
      ((N⁻¹ : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = 1 := by
    rw [← GeneralLinearGroup.coe_mul, mul_inv_cancel, GeneralLinearGroup.coe_one]
  have hMiso : ((((N⁻¹ : GL (HypIndex r 1) K)) :
      Matrix (HypIndex r 1) (HypIndex r 1) K).map h.bar)ᵀ * hypGram r 1 K *
      ((N⁻¹ : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = hypGram r 1 K := by
    have hNsmul : ∀ p q : HypIndex r 1 → K,
        gramForm h (hypGram r 1 K) ((N : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ p)
          ((N : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ q) = gramForm h (hypGram r 1 K) p q :=
      (gramForm_isometry_iff h (hypGram r 1 K)
        (N : Matrix (HypIndex r 1) (HypIndex r 1) K)).mpr hNiso
    have hNmul : ∀ x : HypIndex r 1 → K,
        (N : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ
          (((N⁻¹ : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ x) = x :=
      fun x => by rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
    apply gramForm_injective h
    intro x y
    rw [← gramForm_mulVec h (hypGram r 1 K)
      ((N⁻¹ : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) x y]
    calc gramForm h (hypGram r 1 K)
          (((N⁻¹ : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ x)
          (((N⁻¹ : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ y)
        = gramForm h (hypGram r 1 K)
            ((N : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ
              (((N⁻¹ : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ x))
            ((N : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ
              (((N⁻¹ : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ y)) :=
          (hNsmul _ _).symm
      _ = gramForm h (hypGram r 1 K) x y := by rw [hNmul x, hNmul y]
  have hMv : ((N⁻¹ : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ v =
      (Pi.single (Sum.inr (Sum.inl 0)) 1 : HypIndex r 1 → K) := by
    rw [← hNv, Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]
  obtain ⟨g, a, hg⟩ := ggKGUf_torus_left h hr (N⁻¹) hMiso
  have hDe : diagonal (torusEntries h a (fun _ : Fin 1 => 1)) *ᵥ
      (Pi.single (Sum.inr (Sum.inl 0)) 1 : HypIndex r 1 → K) =
      (Pi.single (Sum.inr (Sum.inl 0)) 1 : HypIndex r 1 → K) := by
    rw [Matrix.mulVec_single_one]
    funext i
    rw [Matrix.col_apply]
    by_cases hi : i = (Sum.inr (Sum.inl 0) : HypIndex r 1)
    · rw [hi, Matrix.diagonal_apply_eq]
      simp [torusEntries]
    · rw [Matrix.diagonal_apply_ne _ hi]
      simp [hi]
  refine ⟨g, ?_⟩
  change ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ v =
    (Pi.single (Sum.inr (Sum.inl 0)) 1 : HypIndex r 1 → K)
  rw [hg, ← Matrix.mulVec_mulVec, hMv, hDe]

end WittTransitivity

open CFSG.Open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  Multiplicative Matrix

private def ggKGUo_c (r : ℕ) : HypIndex r 1 := Sum.inr (Sum.inl 0)

private def ggKGUo_oc (r : ℕ) : HypIndex r 0 → HypIndex r 1
  | .inl i => .inl i
  | .inr (.inl k) => Fin.elim0 k
  | .inr (.inr i) => .inr (.inr i)

private theorem ggKGUo_oc_injective (r : ℕ) : Function.Injective (ggKGUo_oc r) := by
  intro a b h
  rcases a with i | k | i <;> rcases b with j | l | j
  · simpa [ggKGUo_oc] using h
  · exact Fin.elim0 l
  · simp [ggKGUo_oc] at h
  · exact Fin.elim0 k
  · exact Fin.elim0 k
  · exact Fin.elim0 k
  · simp [ggKGUo_oc] at h
  · exact Fin.elim0 l
  · simpa [ggKGUo_oc] using h

private theorem ggKGUo_oc_ne_c (r : ℕ) (a : HypIndex r 0) : ggKGUo_oc r a ≠ ggKGUo_c r := by
  rcases a with i | k | i
  · simp [ggKGUo_oc, ggKGUo_c]
  · exact Fin.elim0 k
  · simp [ggKGUo_oc, ggKGUo_c]

private theorem ggKGUo_c_ne_oc (r : ℕ) (a : HypIndex r 0) : ggKGUo_c r ≠ ggKGUo_oc r a :=
  (ggKGUo_oc_ne_c r a).symm

private def ggKGUo_osplit (r : ℕ) : HypIndex r 1 ≃ HypIndex r 0 ⊕ Unit where
  toFun
    | .inl i => Sum.inl (.inl i)
    | .inr (.inl k) => Sum.inr ()
    | .inr (.inr i) => Sum.inl (.inr (.inr i))
  invFun
    | Sum.inl (.inl i) => .inl i
    | Sum.inl (.inr (.inl k)) => Fin.elim0 k
    | Sum.inl (.inr (.inr i)) => .inr (.inr i)
    | Sum.inr _ => .inr (.inl 0)
  left_inv := by
    intro a
    rcases a with i | k | i
    · rfl
    · fin_cases k; rfl
    · rfl
  right_inv := by
    intro a
    rcases a with (i | k | i) | u
    · rfl
    · exact Fin.elim0 k
    · rfl
    · rfl

private theorem ggKGUo_osplit_apply_oc (r : ℕ) (a : HypIndex r 0) :
    ggKGUo_osplit r (ggKGUo_oc r a) = Sum.inl a := by
  rcases a with i | k | i
  · rfl
  · exact Fin.elim0 k
  · rfl

private theorem ggKGUo_osplit_apply_c (r : ℕ) : ggKGUo_osplit r (ggKGUo_c r) = Sum.inr () := rfl

private theorem ggKGUo_hypGram_split {K : Type} [Field K] (r : ℕ) :
    (hypGram r 1 K).submatrix (ggKGUo_osplit r).symm (ggKGUo_osplit r).symm =
      Matrix.fromBlocks (hypGram r 0 K) 0 0 (1 : Matrix Unit Unit K) := by
  ext a b
  rcases a with (i | k | i) | u <;> rcases b with (j | l | j) | v
  all_goals first | exact Fin.elim0 k | exact Fin.elim0 l | skip
  all_goals simp [Matrix.submatrix_apply, ggKGUo_osplit, hypGram_apply, ggKGUo_c,
    Matrix.fromBlocks, Fin.elim0]

private noncomputable def ggKGUo_betaMatOfMat {K : Type} [Field K] {r : ℕ}
    (B : Matrix (HypIndex r 0) (HypIndex r 0) K) : Matrix (HypIndex r 1) (HypIndex r 1) K :=
  Matrix.reindex (ggKGUo_osplit r).symm (ggKGUo_osplit r).symm
    (Matrix.fromBlocks B 0 0 1)

private noncomputable def ggKGUo_betaMat {K : Type} [Field K] {r : ℕ} (g : GL (HypIndex r 0) K) :
    Matrix (HypIndex r 1) (HypIndex r 1) K :=
  ggKGUo_betaMatOfMat (K := K) (g : Matrix (HypIndex r 0) (HypIndex r 0) K)

private theorem ggKGUo_betaMat_apply_oc_oc {K : Type} [Field K] {r : ℕ} (g : GL (HypIndex r 0) K)
  (a b : HypIndex r 0) :
    ggKGUo_betaMat g (ggKGUo_oc r a) (ggKGUo_oc r b) =
      (g : Matrix (HypIndex r 0) (HypIndex r 0) K) a b := by
  simp
    [ggKGUo_betaMat, ggKGUo_betaMatOfMat, Matrix.reindex_apply, Matrix.submatrix_apply,
    ggKGUo_osplit_apply_oc]

private theorem ggKGUo_betaMat_apply_c_c {K : Type} [Field K] {r : ℕ} (g : GL (HypIndex r 0) K) :
    ggKGUo_betaMat g (ggKGUo_c r) (ggKGUo_c r) = 1 := by
  simp
    [ggKGUo_betaMat, ggKGUo_betaMatOfMat, Matrix.reindex_apply, Matrix.submatrix_apply,
    ggKGUo_osplit_apply_c]

private theorem ggKGUo_betaMat_apply_c_oc {K : Type} [Field K] {r : ℕ} (g : GL (HypIndex r 0) K)
  (b : HypIndex r 0) :
    ggKGUo_betaMat g (ggKGUo_c r) (ggKGUo_oc r b) = 0 := by
  simp
    [ggKGUo_betaMat, ggKGUo_betaMatOfMat, Matrix.reindex_apply, Matrix.submatrix_apply,
    ggKGUo_osplit_apply_oc,
    ggKGUo_osplit_apply_c]

private theorem ggKGUo_betaMat_apply_oc_c {K : Type} [Field K] {r : ℕ} (g : GL (HypIndex r 0) K)
  (a : HypIndex r 0) :
    ggKGUo_betaMat g (ggKGUo_oc r a) (ggKGUo_c r) = 0 := by
  simp
    [ggKGUo_betaMat, ggKGUo_betaMatOfMat, Matrix.reindex_apply, Matrix.submatrix_apply,
    ggKGUo_osplit_apply_oc,
    ggKGUo_osplit_apply_c]

private theorem ggKGUo_betaMat_det_ne_zero {K : Type} [Field K] {r : ℕ} (g : GL (HypIndex r 0) K) :
    (ggKGUo_betaMat g).det ≠ 0 := by
  rw [ggKGUo_betaMat, ggKGUo_betaMatOfMat, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁ (A := (g : Matrix (HypIndex r 0) (HypIndex r 0) K))
      (B := 0) (D := (1 : Matrix Unit Unit K))]
  simp [Matrix.GeneralLinearGroup.det_ne_zero g]

private noncomputable def ggKGUo_betaGL {K : Type} [Field K] {r : ℕ} (g : GL (HypIndex r 0) K) : GL
  (HypIndex r 1) K :=
  GeneralLinearGroup.mkOfDetNeZero (ggKGUo_betaMat g)
    (ggKGUo_betaMat_det_ne_zero g)

private noncomputable def ggKGUo_betaBlock {K : Type} [Field K] {r : ℕ}
    (g : GL (HypIndex r 0) K) : Matrix (HypIndex r 0 ⊕ Unit) (HypIndex r 0 ⊕ Unit) K :=
  Matrix.fromBlocks (g : Matrix (HypIndex r 0) (HypIndex r 0) K) 0 0 1

private noncomputable def ggKGUo_reindexEquiv {K : Type} [Field K] {r : ℕ} :
    Matrix (HypIndex r 0 ⊕ Unit) (HypIndex r 0 ⊕ Unit) K ≃+*
      Matrix (HypIndex r 1) (HypIndex r 1) K :=
  Matrix.reindexRingEquiv K (ggKGUo_osplit r).symm

private theorem ggKGUo_betaMat_eq {K : Type} [Field K] {r : ℕ}
    (g : GL (HypIndex r 0) K) :
    ggKGUo_betaMat (K := K) g = ggKGUo_reindexEquiv (ggKGUo_betaBlock g) := rfl

private theorem ggKGUo_betaBlock_isometry {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g : hypSU h r 0) :
    ((ggKGUo_betaBlock (K := K) (g : GL (HypIndex r 0) K)).map h.bar)ᵀ *
        Matrix.fromBlocks (hypGram r 0 K) 0 0 (1 : Matrix Unit Unit K) *
        ggKGUo_betaBlock (K := K) (g : GL (HypIndex r 0) K) =
      Matrix.fromBlocks (hypGram r 0 K) 0 0 (1 : Matrix Unit Unit K) := by
  have hG := (mem_hypSU.mp g.2).1
  rw [ggKGUo_betaBlock, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  have h0 : (0 : Matrix (HypIndex r 0) Unit K).map h.bar = 0 := by ext a b; simp
  have h0' : ((0 : Matrix Unit (HypIndex r 0) K).map h.bar)ᵀ = 0 := by ext a b; simp
  have h1 : (1 : Matrix Unit Unit K).map h.bar = 1 := by ext a b; simp
  simp only [h0, h0', h1, Matrix.transpose_zero, Matrix.transpose_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]
  rw [hG]

private theorem ggKGUo_betaMat_one {K : Type} [Field K] {r : ℕ} :
    ggKGUo_betaMat (K := K) (1 : GL (HypIndex r 0) K) = 1 := by
  rw [ggKGUo_betaMat_eq,
    show ggKGUo_betaBlock (1 : GL (HypIndex r 0) K) = 1 by
      simp [ggKGUo_betaBlock, Matrix.fromBlocks_one],
    map_one]

private theorem ggKGUo_betaMat_mul {K : Type} [Field K] {r : ℕ}
    (g g' : GL (HypIndex r 0) K) :
    ggKGUo_betaMat (K := K) (g * g') = ggKGUo_betaMat g * ggKGUo_betaMat g' := by
  rw [ggKGUo_betaMat_eq, ggKGUo_betaMat_eq, ggKGUo_betaMat_eq,
    show ggKGUo_betaBlock (g * g') = ggKGUo_betaBlock g * ggKGUo_betaBlock g' by
      simp [ggKGUo_betaBlock, Matrix.fromBlocks_multiply],
    map_mul]
private noncomputable def ggKGUo_eC {K : Type} [Field K] {r : ℕ} : HypIndex r 1 → K :=
  Pi.single (ggKGUo_c r) 1

private theorem ggKGUo_betaMat_mulVec_c {K : Type} [Field K] {r : ℕ}
    (g : GL (HypIndex r 0) K) :
    ggKGUo_betaMat (K := K) g *ᵥ ggKGUo_eC (K := K) = ggKGUo_eC (K := K) := by
  rw [ggKGUo_eC, Matrix.mulVec_single_one]
  funext a
  rcases a with i | k | i
  · simpa [ggKGUo_oc, ggKGUo_eC, ggKGUo_c] using
      ggKGUo_betaMat_apply_oc_c (K := K) g (Sum.inl i)
  · fin_cases k
    simpa [ggKGUo_eC, ggKGUo_c] using ggKGUo_betaMat_apply_c_c (K := K) g
  · simpa [ggKGUo_oc, ggKGUo_eC, ggKGUo_c] using
      ggKGUo_betaMat_apply_oc_c (K := K) g (Sum.inr (Sum.inr i))

private theorem ggKGUo_col_c_eq {K : Type} [Field K] {r : ℕ}
    (G : Matrix (HypIndex r 1) (HypIndex r 1) K)
    (hfix : G *ᵥ ggKGUo_eC (K := K) = ggKGUo_eC (K := K)) (a : HypIndex r 1) :
    G a (ggKGUo_c r) = if a = ggKGUo_c r then 1 else 0 := by
  have h := congrFun hfix a
  rw [ggKGUo_eC, Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [h]
  by_cases ha : a = ggKGUo_c r
  · subst ha; simp [ggKGUo_eC]
  · rw [if_neg ha]; simp [ggKGUo_eC, ha]

private theorem ggKGUo_hypPartner_c {r : ℕ} :
    hypPartner (ggKGUo_c r) = ggKGUo_c r := rfl

private theorem ggKGUo_hypGram_mulVec_eC {K : Type} [Field K] {r : ℕ} :
    hypGram r 1 K *ᵥ ggKGUo_eC (K := K) = ggKGUo_eC (K := K) := by
  funext a
  rw [hypGram_mulVec]
  by_cases ha : a = ggKGUo_c r
  · subst ha
    simp [ggKGUo_eC, ggKGUo_hypPartner_c]
  · have hpa : hypPartner a ≠ ggKGUo_c r := fun hc => ha (by
      rw [← hypPartner_hypPartner a, hc, ggKGUo_hypPartner_c])
    simp [ggKGUo_eC, ha, hpa]

private theorem ggKGUo_row_c_eq {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g : hypSU h r 1)
    (hfix : (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ ggKGUo_eC (K := K) =
      ggKGUo_eC (K := K)) (a : HypIndex r 1) :
    (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) (ggKGUo_c r) a =
      if a = ggKGUo_c r then 1 else 0 := by
  let G : Matrix (HypIndex r 1) (HypIndex r 1) K :=
    ((g : hypSU h r 1) : GL (HypIndex r 1) K)
  have hG := (mem_hypSU.mp g.2).1
  have hfix' : G *ᵥ ggKGUo_eC (K := K) = ggKGUo_eC (K := K) := by
    change (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ ggKGUo_eC (K := K) =
      ggKGUo_eC (K := K)
    exact hfix
  have h1 : ((G.map h.bar)ᵀ *ᵥ ggKGUo_eC (K := K)) = ggKGUo_eC (K := K) := by
    have h2 : (((G.map h.bar)ᵀ * hypGram r 1 K * G) *ᵥ ggKGUo_eC (K := K)) =
        hypGram r 1 K *ᵥ ggKGUo_eC (K := K) := by rw [hG]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfix',
      ggKGUo_hypGram_mulVec_eC] at h2
    exact h2
  rw [ggKGUo_eC] at h1
  have hh := congrFun h1 a
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply,
    Matrix.map_apply] at hh
  change h.bar (G (ggKGUo_c r) a) = ggKGUo_eC (K := K) a at hh
  apply h.bar.injective
  by_cases ha : a = ggKGUo_c r
  · subst ha
    simpa [ggKGUo_eC, map_one] using hh
  · simpa [ggKGUo_eC, ha, map_zero] using hh

private noncomputable def ggKGUo_delMat {K : Type} {r : ℕ}
    (G : Matrix (HypIndex r 1) (HypIndex r 1) K) :
    Matrix (HypIndex r 0) (HypIndex r 0) K :=
  fun a b => G (ggKGUo_oc r a) (ggKGUo_oc r b)

private theorem ggKGUo_betaMatOfMat_delMat {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g : hypSU h r 1)
    (hfix : (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ ggKGUo_eC (K := K) =
      ggKGUo_eC (K := K)) :
    ggKGUo_betaMatOfMat (K := K) (ggKGUo_delMat (K := K)
      (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
        Matrix (HypIndex r 1) (HypIndex r 1) K)) =
      (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
        Matrix (HypIndex r 1) (HypIndex r 1) K) := by
  let G : Matrix (HypIndex r 1) (HypIndex r 1) K :=
    (((g : hypSU h r 1) : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K)
  have hfix' : G *ᵥ ggKGUo_eC (K := K) = ggKGUo_eC (K := K) := hfix
  have hcol := fun a => ggKGUo_col_c_eq G hfix' a
  have hrow := fun a => ggKGUo_row_c_eq h g hfix a
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j
  · simp [ggKGUo_betaMatOfMat, ggKGUo_delMat, ggKGUo_osplit, ggKGUo_oc]
  · have h1 : G (Sum.inl i) (ggKGUo_c r) = 0 := by
      have := hcol (Sum.inl i)
      simpa [ggKGUo_c] using this
    fin_cases l
    simpa [ggKGUo_betaMatOfMat, ggKGUo_osplit, ggKGUo_c, Matrix.submatrix_apply] using h1.symm
  · simp [ggKGUo_betaMatOfMat, ggKGUo_delMat, ggKGUo_osplit, ggKGUo_oc]
  · have h1 : G (ggKGUo_c r) (Sum.inl j) = 0 := by
      have := hrow (Sum.inl j)
      simpa [ggKGUo_c] using this
    fin_cases k
    simpa [ggKGUo_betaMatOfMat, ggKGUo_osplit, ggKGUo_c, Matrix.submatrix_apply] using h1.symm
  · have h1 : G (ggKGUo_c r) (ggKGUo_c r) = 1 := by
      have := hcol (ggKGUo_c r)
      simpa using this
    fin_cases k
    fin_cases l
    simpa [ggKGUo_betaMatOfMat, ggKGUo_osplit, ggKGUo_c, Matrix.submatrix_apply] using h1.symm
  · have h1 : G (ggKGUo_c r) (Sum.inr (Sum.inr j)) = 0 := by
      have := hrow (Sum.inr (Sum.inr j))
      simpa [ggKGUo_c] using this
    fin_cases k
    simpa [ggKGUo_betaMatOfMat, ggKGUo_osplit, ggKGUo_c, Matrix.submatrix_apply] using h1.symm
  · simp [ggKGUo_betaMatOfMat, ggKGUo_delMat, ggKGUo_osplit, ggKGUo_oc]
  · have h1 : G (Sum.inr (Sum.inr i)) (ggKGUo_c r) = 0 := by
      have := hcol (Sum.inr (Sum.inr i))
      simpa [ggKGUo_c] using this
    fin_cases l
    simpa [ggKGUo_betaMatOfMat, ggKGUo_osplit, ggKGUo_c, Matrix.submatrix_apply] using h1.symm
  · simp [ggKGUo_betaMatOfMat, ggKGUo_delMat, ggKGUo_osplit, ggKGUo_oc]

private theorem ggKGUo_osplit_symm_inl {r : ℕ} (a : HypIndex r 0) :
    (ggKGUo_osplit r).symm (Sum.inl a) = ggKGUo_oc r a := by
  rcases a with i | k | i <;> rfl

private theorem ggKGUo_osplit_symm_unit {r : ℕ} :
    (ggKGUo_osplit r).symm (Sum.inr ()) = ggKGUo_c r := rfl

private theorem ggKGUo_sum_hypIndex {r : ℕ} {M : Type*} [AddCommMonoid M]
    (f : HypIndex r 1 → M) :
    ∑ a, f a = (∑ b : HypIndex r 0, f (ggKGUo_oc r b)) + f (ggKGUo_c r) := by
  rw [← Equiv.sum_comp (ggKGUo_osplit r).symm f]
  rw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    rw [ggKGUo_osplit_symm_inl]
  · simp [ggKGUo_osplit_symm_unit]

private theorem ggKGUo_reindexEquiv_blockJ {K : Type} [Field K] {r : ℕ} :
    ggKGUo_reindexEquiv (K := K) (Matrix.fromBlocks (hypGram r 0 K) 0 0
      (1 : Matrix Unit Unit K)) = hypGram r 1 K := by
  ext a b
  simp only [ggKGUo_reindexEquiv, Matrix.coe_reindexRingEquiv, Matrix.reindex_apply]
  rw [← ggKGUo_hypGram_split (K := K) r]
  simp [Matrix.submatrix_apply]

private theorem ggKGUo_reindexEquiv_map_bar {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K)
    (A : Matrix (HypIndex r 0 ⊕ Unit) (HypIndex r 0 ⊕ Unit) K) :
    (ggKGUo_reindexEquiv (K := K) A).map h.bar =
      ggKGUo_reindexEquiv (K := K) (A.map h.bar) := by
  ext a b
  simp [ggKGUo_reindexEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]

private theorem ggKGUo_reindexEquiv_transpose {K : Type} [Field K] {r : ℕ}
    (A : Matrix (HypIndex r 0 ⊕ Unit) (HypIndex r 0 ⊕ Unit) K) :
    (ggKGUo_reindexEquiv (K := K) A)ᵀ = ggKGUo_reindexEquiv (K := K) Aᵀ := by
  ext a b
  simp [ggKGUo_reindexEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.transpose_apply]

private theorem ggKGUo_delMat_isometry {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g : hypSU h r 1)
    (hfix : (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ ggKGUo_eC (K := K) =
      ggKGUo_eC (K := K)) :
    ((ggKGUo_delMat (K := K) (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
        Matrix (HypIndex r 1) (HypIndex r 1) K)).map h.bar)ᵀ * hypGram r 0 K *
      ggKGUo_delMat (K := K) (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
        Matrix (HypIndex r 1) (HypIndex r 1) K) = hypGram r 0 K := by
  set B : Matrix (HypIndex r 0) (HypIndex r 0) K :=
    ggKGUo_delMat (K := K) (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) with hB
  have hbeta := ggKGUo_betaMatOfMat_delMat h g hfix
  have hG := (mem_hypSU.mp g.2).1
  have hblock : ((Matrix.fromBlocks B 0 0 (1 : Matrix Unit Unit K)).map h.bar)ᵀ *
      Matrix.fromBlocks (hypGram r 0 K) 0 0 (1 : Matrix Unit Unit K) *
      Matrix.fromBlocks B 0 0 (1 : Matrix Unit Unit K) =
      Matrix.fromBlocks (hypGram r 0 K) 0 0 (1 : Matrix Unit Unit K) := by
    have hthis := hG
    rw [← hbeta] at hthis
    have hR : (ggKGUo_reindexEquiv (K := K))
        (((Matrix.fromBlocks B 0 0 (1 : Matrix Unit Unit K)).map h.bar)ᵀ *
          Matrix.fromBlocks (hypGram r 0 K) 0 0 (1 : Matrix Unit Unit K) *
          Matrix.fromBlocks B 0 0 (1 : Matrix Unit Unit K)) =
        (ggKGUo_reindexEquiv (K := K))
          (Matrix.fromBlocks (hypGram r 0 K) 0 0 (1 : Matrix Unit Unit K)) := by
      simp only [map_mul, ggKGUo_reindexEquiv_transpose, ggKGUo_reindexEquiv_map_bar h,
        ggKGUo_reindexEquiv_blockJ]
      exact hthis
    exact (ggKGUo_reindexEquiv (K := K)).injective hR
  have h0 : (0 : Matrix (HypIndex r 0) Unit K).map h.bar = 0 := by ext a b; simp
  have h0' : ((0 : Matrix Unit (HypIndex r 0) K).map h.bar)ᵀ = 0 := by ext a b; simp
  have h1 : (1 : Matrix Unit Unit K).map h.bar = 1 := by ext a b; simp
  have hblock' : Matrix.fromBlocks
      (((B.map h.bar)ᵀ * hypGram r 0 K) * B) 0 0 (1 : Matrix Unit Unit K) =
      Matrix.fromBlocks (hypGram r 0 K) 0 0 (1 : Matrix Unit Unit K) := by
    simpa only [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      h0, h0', h1, Matrix.transpose_zero, Matrix.transpose_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one] using hblock
  have htop := (Matrix.fromBlocks_inj.mp hblock').1
  simpa [hB, Matrix.mul_assoc] using htop

private theorem ggKGUo_betaGL_mem {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g : hypSU h r 0) :
    ggKGUo_betaGL (K := K) (g : GL (HypIndex r 0) K) ∈ hypSU h r 1 := by
  have hblock := ggKGUo_betaBlock_isometry h g
  rw [mem_hypSU]
  constructor
  · change ((ggKGUo_betaMat (K := K) (g : GL (HypIndex r 0) K)).map h.bar)ᵀ *
        hypGram r 1 K * ggKGUo_betaMat (K := K) (g : GL (HypIndex r 0) K) = hypGram r 1 K
    rw [ggKGUo_betaMat_eq, ← ggKGUo_reindexEquiv_blockJ]
    simp only [ggKGUo_reindexEquiv_map_bar h, ggKGUo_reindexEquiv_transpose, ← map_mul, hblock]
  · change (ggKGUo_betaMat (K := K) (g : GL (HypIndex r 0) K)).det = 1
    rw [ggKGUo_betaMat_eq,
      show (ggKGUo_reindexEquiv (K := K) (ggKGUo_betaBlock (g : GL (HypIndex r 0) K))).det =
          (ggKGUo_betaBlock (g : GL (HypIndex r 0) K)).det from by
        simpa [ggKGUo_reindexEquiv] using
          Matrix.det_reindex_self (K := K) (ggKGUo_osplit r).symm
            (ggKGUo_betaBlock (g : GL (HypIndex r 0) K)),
      ggKGUo_betaBlock, Matrix.det_fromBlocks_zero₂₁]
    simp [(mem_hypSU.mp g.2).2]

private noncomputable def ggKGUo_beta {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g : hypSU h r 0) : hypSU h r 1 :=
  ⟨ggKGUo_betaGL (K := K) (g : GL (HypIndex r 0) K), ggKGUo_betaGL_mem h g⟩

private theorem ggKGUo_beta_one {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) : ggKGUo_beta h (1 : hypSU h r 0) = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact ggKGUo_betaMat_one

private theorem ggKGUo_beta_mul {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g g' : hypSU h r 0) :
    ggKGUo_beta h (g * g') = ggKGUo_beta h g * ggKGUo_beta h g' := by
  apply Subtype.ext
  apply Units.ext
  exact ggKGUo_betaMat_mul (g : GL (HypIndex r 0) K) (g' : GL (HypIndex r 0) K)

private noncomputable def ggKGUo_betaHom {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) : hypSU h r 0 →* hypSU h r 1 where
  toFun := ggKGUo_beta h
  map_one' := ggKGUo_beta_one h
  map_mul' := ggKGUo_beta_mul h

private theorem ggKGUo_beta_smul_c {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g : hypSU h r 0) :
    ggKGUo_beta (r := r) h g • ggKGUo_eC (K := K) (r := r) = ggKGUo_eC (K := K) (r := r) := by
  change ((ggKGUo_betaGL (K := K) (r := r) (g : GL (HypIndex r 0) K) : GL (HypIndex r 1) K) :
    Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ ggKGUo_eC (K := K) = ggKGUo_eC (K := K)
  exact ggKGUo_betaMat_mulVec_c (K := K) (r := r) (g : GL (HypIndex r 0) K)

private theorem ggKGUo_det_ne_zero_of_isometry {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (M : Matrix (HypIndex r 1) (HypIndex r 1) K)
    (hM : (M.map h.bar)ᵀ * hypGram r 1 K * M = hypGram r 1 K) : M.det ≠ 0 := by
  have hmap : (M.map h.bar).det = h.bar M.det := (RingHom.map_det h.bar M).symm
  have h := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmap] at h
  intro h0
  rw [h0] at h
  simp only [map_zero, zero_mul] at h
  exact det_hypGram_ne_zero h.symm

private theorem ggKGUo_det_betaMatOfMat {K : Type} [Field K] {r : ℕ}
    (B : Matrix (HypIndex r 0) (HypIndex r 0) K) :
    (ggKGUo_betaMatOfMat (K := K) B).det = B.det := by
  rw [ggKGUo_betaMatOfMat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simp

private noncomputable def ggKGUo_delGL {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g : hypSU h r 1)
    (hfix : (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ ggKGUo_eC (K := K) =
      ggKGUo_eC (K := K)) : GL (HypIndex r 0) K :=
  let B : Matrix (HypIndex r 0) (HypIndex r 0) K :=
    ggKGUo_delMat (K := K) (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K)
  have hbeta : ggKGUo_betaMatOfMat (K := K) B =
      (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
        Matrix (HypIndex r 1) (HypIndex r 1) K) :=
    ggKGUo_betaMatOfMat_delMat h g hfix
  have hdetBeta : (ggKGUo_betaMatOfMat (K := K) B).det = B.det := by
    rw [ggKGUo_betaMatOfMat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hB : B.det ≠ 0 := by
    rw [← hdetBeta, hbeta, (mem_hypSU.mp g.2).2]
    exact one_ne_zero
  GeneralLinearGroup.mkOfDetNeZero B hB

private theorem ggKGUo_delGL_mem {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g : hypSU h r 1)
    (hfix : (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ ggKGUo_eC (K := K) =
      ggKGUo_eC (K := K)) : ggKGUo_delGL h g hfix ∈ hypSU h r 0 := by
  have hbeta : ggKGUo_betaMat (K := K) (ggKGUo_delGL h g hfix) =
      (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
        Matrix (HypIndex r 1) (HypIndex r 1) K) := by
    change ggKGUo_betaMatOfMat (K := K)
      ((ggKGUo_delGL h g hfix : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) = _
    exact ggKGUo_betaMatOfMat_delMat h g hfix
  have hdet : (ggKGUo_delGL h g hfix : Matrix (HypIndex r 0) (HypIndex r 0) K).det = 1 := by
    rw [← ggKGUo_det_betaMatOfMat (K := K)
      ((ggKGUo_delGL h g hfix : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K)]
    rw [← show ggKGUo_betaMat (K := K) (ggKGUo_delGL h g hfix) =
      ggKGUo_betaMatOfMat (K := K)
        ((ggKGUo_delGL h g hfix : GL (HypIndex r 0) K) :
          Matrix (HypIndex r 0) (HypIndex r 0) K) from rfl]
    rw [hbeta, (mem_hypSU.mp g.2).2]
  refine mem_hypSU.mpr ⟨?_, hdet⟩
  change ((ggKGUo_delMat (K := K) (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K)).map h.bar)ᵀ * hypGram r 0 K *
    ggKGUo_delMat (K := K) (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) = hypGram r 0 K
  exact ggKGUo_delMat_isometry h g hfix

private noncomputable def ggKGUo_delSU {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g : hypSU h r 1)
    (hfix : (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ ggKGUo_eC (K := K) =
      ggKGUo_eC (K := K)) : hypSU h r 0 :=
  ⟨ggKGUo_delGL h g hfix, ggKGUo_delGL_mem h g hfix⟩

private theorem ggKGUo_delSU_eq {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g : hypSU h r 1)
    (hfix : (((g : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ ggKGUo_eC (K := K) =
      ggKGUo_eC (K := K)) :
    ggKGUo_beta h (ggKGUo_delSU h g hfix) = g := by
  apply Subtype.ext
  apply Units.ext
  exact ggKGUo_betaMatOfMat_delMat h g hfix

private theorem ggKGUo_mem_range_beta_iff {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g : hypSU h r 1) :
    g ∈ (ggKGUo_betaHom h).range ↔
      g • ggKGUo_eC (K := K) (r := r) = ggKGUo_eC (K := K) (r := r) := by
  constructor
  · rintro ⟨g0, rfl⟩
    exact ggKGUo_beta_smul_c h g0
  · intro hfix
    exact ⟨ggKGUo_delSU h g hfix, ggKGUo_delSU_eq h g hfix⟩

private structure ggKGUo_OddFrame {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (E : Subgroup (hypSU h r 1)) where
  N : GL (HypIndex r 1) K
  χ : E →* (HypIndex r 1 → Kˣ)
  inj : Function.Injective χ
  pow : ∀ (x : E) (i : HypIndex r 1), χ x i ^ p = 1
  conj : ∀ x : E,
    (((x : hypSU h r 1) : GL (HypIndex r 1) K) :
        Matrix (HypIndex r 1) (HypIndex r 1) K) *
        (N : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      (N : Matrix (HypIndex r 1) (HypIndex r 1) K) *
        diagonal (fun i => ((χ x i : Kˣ) : K))

private noncomputable def ggKGUo_OddFrame.gram {n r p : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 n K} {E : Subgroup (hypSU h r 1)}
    (F : ggKGUo_OddFrame (p := p) h E) : Matrix (HypIndex r 1) (HypIndex r 1) K :=
  (((F.N : Matrix (HypIndex r 1) (HypIndex r 1) K).map h.bar)ᵀ * hypGram r 1 K) *
    (F.N : Matrix (HypIndex r 1) (HypIndex r 1) K)

private theorem ggKGUo_exists_oddFrame {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hpq : p ∣ 2 ^ n - 1)
    (E : Subgroup (hypSU h r 1)) (hE : IsElemAbelian p E) :
    Nonempty (ggKGUo_OddFrame (p := p) h E) := by
  classical
  haveI : Finite K := h.finite
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let φ : E →* GL (HypIndex r 1) K := (hypSU h r 1).subtype.comp E.subtype
  let S : Set (GL (HypIndex r 1) K) := Set.range φ
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    exact congrArg (fun z : hypSU h r 1 => (z : GL (HypIndex r 1) K))
      (TableB.IsElemAbelian.comm hE a.2 b.2)
  have hpow : ∀ x ∈ S, x ^ p = 1 := by
    rintro x ⟨a, rfl⟩
    exact congrArg (fun z : hypSU h r 1 => (z : GL (HypIndex r 1) K)) (hE.2 a a.2)
  obtain ⟨A, hA⟩ := TypeA.PGLTor.exists_conj_diagonal hζ S hcomm hpow
  let Dg : E →* GL (HypIndex r 1) K := (MulAut.conj A).toMonoidHom.comp φ
  let D : E → Matrix (HypIndex r 1) (HypIndex r 1) K := fun x => (Dg x : Matrix _ _ K)
  have hDdiag : ∀ x : E, D x = diagonal (fun i => D x i i) := by
    intro x
    ext i j
    by_cases hij : i = j
    · subst hij; rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij]
      exact hA (φ x) (Set.mem_range.mpr ⟨x, rfl⟩) i j hij
  have hunit : ∀ x : E, IsUnit (D x) := by
    intro x
    exact IsUnit.mul (IsUnit.mul ⟨A, rfl⟩ ⟨φ x, rfl⟩) ⟨A⁻¹, rfl⟩
  have hd_ne : ∀ (x : E) (i : HypIndex r 1), D x i i ≠ 0 := by
    intro x i
    have h1 : IsUnit (diagonal (fun i => D x i i)) := hDdiag x ▸ hunit x
    have h2 : IsUnit ((fun i => D x i i) i) := (Matrix.isUnit_diagonal.mp h1).apply i
    exact isUnit_iff_ne_zero.mp h2
  have hDmul : ∀ x y : E, D (x * y) = D x * D y := by
    intro x y
    simp only [D, map_mul, Units.val_mul]
  have hDmul_apply : ∀ (x y : E) (i : HypIndex r 1),
      D (x * y) i i = D x i i * D y i i := by
    intro x y i
    rw [hDmul]
    conv_lhs => rw [hDdiag x, hDdiag y]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]
  have hD1 : D 1 = 1 := by
    show ((Dg 1 : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = 1
    rw [map_one, Units.val_one]
  let χ : E →* (HypIndex r 1 → Kˣ) :=
    { toFun := fun x i => Units.mk0 (D x i i) (hd_ne x i)
      map_one' := by
        ext i
        show D 1 i i = 1
        rw [hD1, Matrix.one_apply_eq]
      map_mul' := by
        intro x y
        ext i
        show D (x * y) i i = D x i i * D y i i
        exact hDmul_apply x y i }
  have hχpow : ∀ (x : E) (i : HypIndex r 1), χ x i ^ p = 1 := by
    intro x i
    apply Units.ext
    show (D x i i) ^ p = 1
    have hxp : x ^ p = 1 := Subtype.ext (by simpa using hE.2 (x : hypSU h r 1) x.2)
    have hDgp : Dg x ^ p = 1 := by rw [← map_pow, hxp, map_one]
    have hDpow : D x ^ p = 1 := by
      rw [show D x = (Dg x : Matrix (HypIndex r 1) (HypIndex r 1) K) from rfl,
        ← Units.val_pow_eq_pow_val, hDgp, Units.val_one]
    have hdiag : diagonal (fun i => D x i i ^ p) = (1 : Matrix _ _ K) := by
      have h2 : diagonal (fun i => D x i i) ^ p = 1 := by
        rw [← hDdiag x, hDpow]
      rw [Matrix.diagonal_pow] at h2
      exact h2
    have := congrFun (congrFun hdiag i) i
    simpa [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using this
  have hDg_diag : ∀ x : E, (Dg x : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      diagonal (fun i => ((χ x i : Kˣ) : K)) := by
    intro x
    have hfun : (fun i => ((χ x i : Kˣ) : K)) = fun i => D x i i := rfl
    rw [hfun]
    exact hDdiag x
  have hinj : Function.Injective χ := by
    intro x y hxy
    have hDg : Dg x = Dg y := by
      apply Units.ext
      rw [hDg_diag x, hDg_diag y, hxy]
    have hφ : φ x = φ y := by
      apply (MulAut.conj A).injective
      exact hDg
    exact Subtype.ext (Subtype.ext hφ)
  refine ⟨A⁻¹, χ, hinj, hχpow, ?_⟩
  intro x
  have hgl : (A⁻¹ : GL (HypIndex r 1) K) * Dg x = φ x * A⁻¹ := by
    show (A⁻¹ : GL (HypIndex r 1) K) * (A * φ x * A⁻¹) = φ x * A⁻¹
    group
  have hmat : ((A⁻¹ : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) *
        ((Dg x : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      ((φ x : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) *
        ((A⁻¹ : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) := by
    simpa only [Units.val_mul] using
      congrArg (fun u : GL (HypIndex r 1) K => (u : Matrix (HypIndex r 1) (HypIndex r 1) K)) hgl
  rw [← hDg_diag x]
  exact hmat.symm

private theorem ggKGUo_odd_chi_mul_chi {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n - 1)
    {E : Subgroup (hypSU h r 1)} (F : ggKGUo_OddFrame (p := p) h E)
    {i j : HypIndex r 1} (hij : F.gram i j ≠ 0) (x : E) :
    F.χ x i * F.χ x j = 1 := by
  let N : Matrix (HypIndex r 1) (HypIndex r 1) K := (F.N : Matrix _ _ K)
  let xm : Matrix (HypIndex r 1) (HypIndex r 1) K :=
    (((x : hypSU h r 1) : GL (HypIndex r 1) K) : Matrix _ _ K)
  let D : Matrix (HypIndex r 1) (HypIndex r 1) K :=
    diagonal (fun i => ((F.χ x i : Kˣ) : K))
  have hconj : xm * N = N * D := F.conj x
  have h1 : (N.map h.bar)ᵀ * (xm.map h.bar)ᵀ = (D.map h.bar)ᵀ * (N.map h.bar)ᵀ := by
    have hh := congrArg (fun M : Matrix (HypIndex r 1) (HypIndex r 1) K => (M.map h.bar)ᵀ) hconj
    rwa [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul] at hh
  have hxJ : (xm.map h.bar)ᵀ * hypGram r 1 K * xm = hypGram r 1 K :=
    (mem_hypSU.mp (x : hypSU h r 1).2).1
  have hmid : (D.map h.bar)ᵀ * ((N.map h.bar)ᵀ * hypGram r 1 K * N) * D =
      (N.map h.bar)ᵀ * ((xm.map h.bar)ᵀ * hypGram r 1 K * xm) * N := by
    calc (D.map h.bar)ᵀ * ((N.map h.bar)ᵀ * hypGram r 1 K * N) * D
        = ((D.map h.bar)ᵀ * (N.map h.bar)ᵀ) * hypGram r 1 K * (N * D) := by
          simp only [Matrix.mul_assoc]
      _ = ((N.map h.bar)ᵀ * (xm.map h.bar)ᵀ) * hypGram r 1 K * (xm * N) := by
          rw [← h1, ← hconj]
      _ = (N.map h.bar)ᵀ * ((xm.map h.bar)ᵀ * hypGram r 1 K * xm) * N := by
          simp only [Matrix.mul_assoc]
  have hkey : (D.map h.bar)ᵀ * F.gram * D = F.gram := by
    show (D.map h.bar)ᵀ * ((N.map h.bar)ᵀ * hypGram r 1 K * N) * D =
      (N.map h.bar)ᵀ * hypGram r 1 K * N
    calc (D.map h.bar)ᵀ * ((N.map h.bar)ᵀ * hypGram r 1 K * N) * D
        = (N.map h.bar)ᵀ * ((xm.map h.bar)ᵀ * hypGram r 1 K * xm) * N := hmid
      _ = (N.map h.bar)ᵀ * hypGram r 1 K * N := by rw [hxJ]
  have hentry : ((D.map h.bar)ᵀ * F.gram * D) i j =
      h.bar ((F.χ x i : Kˣ) : K) * F.gram i j * ((F.χ x j : Kˣ) : K) := by
    simp only [D, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hgram_eq : h.bar ((F.χ x i : Kˣ) : K) * F.gram i j * ((F.χ x j : Kˣ) : K) =
      F.gram i j := by
    rw [← hentry, hkey]
  have hbar_di : h.bar ((F.χ x i : Kˣ) : K) = ((F.χ x i : Kˣ) : K) := by
    refine bar_eq_self_of_pow_eq_one h hpq ?_
    have := congrArg (fun u : Kˣ => (u : K)) (F.pow x i)
    simpa [Units.val_pow_eq_pow_val] using this
  exact Units.ext (by
    rw [Units.val_mul, Units.val_one, ← hbar_di]
    have h2 : (h.bar ((F.χ x i : Kˣ) : K) * ((F.χ x j : Kˣ) : K)) * F.gram i j =
        1 * F.gram i j := by
      rw [one_mul]
      calc (h.bar ((F.χ x i : Kˣ) : K) * ((F.χ x j : Kˣ) : K)) * F.gram i j
          = h.bar ((F.χ x i : Kˣ) : K) * F.gram i j * ((F.χ x j : Kˣ) : K) := by ring
        _ = F.gram i j := hgram_eq
    exact mul_right_cancel₀ hij h2)

private theorem ggKGUo_odd_exists_antisymm_perm {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n - 1)
    {E : Subgroup (hypSU h r 1)} (F : ggKGUo_OddFrame (p := p) h E) :
    ∃ τ : Equiv.Perm (HypIndex r 1), (∀ i, F.gram i (τ i) ≠ 0) ∧
      ∀ (x : E) (i : HypIndex r 1), F.χ x (τ i) = (F.χ x i)⁻¹ := by
  have hdet : F.gram.det ≠ 0 := by
    have hN : (F.N : Matrix (HypIndex r 1) (HypIndex r 1) K).det ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero F.N
    have hNmap : ((F.N : Matrix (HypIndex r 1) (HypIndex r 1) K).map h.bar).det ≠ 0 := by
      have hmap := (RingHom.map_det h.bar (F.N : Matrix (HypIndex r 1) (HypIndex r 1) K)).symm
      rw [show h.bar.mapMatrix (F.N : Matrix (HypIndex r 1) (HypIndex r 1) K) =
        (F.N : Matrix (HypIndex r 1) (HypIndex r 1) K).map h.bar from rfl] at hmap
      rw [hmap]
      intro hz
      exact hN (h.bar.injective (by rw [hz, map_zero]))
    show ((((F.N : Matrix (HypIndex r 1) (HypIndex r 1) K).map h.bar)ᵀ * hypGram r 1 K) *
      (F.N : Matrix (HypIndex r 1) (HypIndex r 1) K)).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hNmap det_hypGram_ne_zero) hN
  obtain ⟨σ, hσ⟩ := exists_perm_ne_zero_of_det_ne_zero hdet
  have hHerm : (F.gram.map h.bar)ᵀ = F.gram := by
    have hstarN : ((((F.N : Matrix (HypIndex r 1) (HypIndex r 1) K).map h.bar)ᵀ).map h.bar)ᵀ =
        (F.N : Matrix (HypIndex r 1) (HypIndex r 1) K) := by
      rw [Matrix.transpose_map, Matrix.transpose_transpose, Matrix.map_map,
        show h.bar ∘ h.bar = id from funext h.bar_bar, Matrix.map_id]
    show (((((F.N : Matrix (HypIndex r 1) (HypIndex r 1) K).map h.bar)ᵀ * hypGram r 1 K) *
      (F.N : Matrix (HypIndex r 1) (HypIndex r 1) K)).map h.bar)ᵀ = F.gram
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      hypGram_conjTranspose, hstarN]
    simp only [ggKGUo_OddFrame.gram, Matrix.mul_assoc]
  refine ⟨σ, ?_, ?_⟩
  · intro i
    have hpos := hσ i
    intro hzero
    apply hpos
    have hentry := congrFun (congrFun hHerm (σ i)) i
    rw [Matrix.transpose_apply, Matrix.map_apply, hzero, map_zero] at hentry
    exact hentry.symm
  · intro x i
    exact eq_inv_of_mul_eq_one_left (ggKGUo_odd_chi_mul_chi h hpq F (hσ i) x)

private theorem ggKGUo_multiset_even_sum {s : Multiset ℕ}
    (h : ∀ x ∈ s, Even x) : Even s.sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons]
    exact Even.add (h a (Multiset.mem_cons_self a s))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

private theorem ggKGUo_mem_cycleType_minimalPeriod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Equiv.Perm ι) {n : ℕ} (hn : n ∈ τ.cycleType) :
    ∃ i, Function.minimalPeriod τ i = n := by
  classical
  have hcount : 0 < τ.cycleType.count n := Multiset.count_pos.mpr hn
  rw [Equiv.Perm.CycleType.count_def] at hcount
  obtain ⟨c⟩ := Fintype.card_pos_iff.mp hcount
  have hc : (c : τ.cycleFactorsFinset).1 ∈ τ.cycleFactorsFinset := (c : τ.cycleFactorsFinset).2
  have hcyc : (c : τ.cycleFactorsFinset).1.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
  obtain ⟨a, ha⟩ := hcyc.nonempty_support
  refine ⟨a, ?_⟩
  have hcycOn := Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset hc
  have hdvd1 : Function.minimalPeriod τ a ∣ (c : τ.cycleFactorsFinset).1.support.card := by
    rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
    exact Equiv.Perm.IsCycleOn.pow_card_apply hcycOn ha
  have hdvd2 : (c : τ.cycleFactorsFinset).1.support.card ∣ Function.minimalPeriod τ a := by
    rw [← Equiv.Perm.IsCycleOn.pow_apply_eq hcycOn ha]
    exact Function.isPeriodicPt_minimalPeriod τ a
  have heq : Function.minimalPeriod τ a = (c : τ.cycleFactorsFinset).1.support.card :=
    Nat.dvd_antisymm hdvd1 hdvd2
  rw [heq, c.2]

private theorem ggKGUo_exists_odd_minimalPeriod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Equiv.Perm ι) (hcard : Odd (Fintype.card ι)) :
    ∃ i, Odd (Function.minimalPeriod τ i) := by
  classical
  by_contra hcon
  push Not at hcon
  have hall : ∀ i, Even (Function.minimalPeriod τ i) := fun i =>
    Nat.not_odd_iff_even.mp (hcon i)
  have hnoFix : ∀ i, τ i ≠ i := by
    intro i hi
    have h1 : Function.minimalPeriod τ i = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hi
    have h2 := hall i
    rw [h1] at h2
    exact Nat.not_even_one h2
  have hsupp : τ.support = Finset.univ := by
    ext i
    rw [Equiv.Perm.mem_support]
    exact ⟨fun _ => Finset.mem_univ i, fun _ => hnoFix i⟩
  have hparts : τ.partition.parts = τ.cycleType := by
    rw [Equiv.Perm.parts_partition]
    have hcard_supp : Fintype.card ι = τ.support.card := by
      rw [hsupp, Finset.card_univ]
    rw [hcard_supp, Nat.sub_self, Multiset.replicate_zero, add_zero]
  have halleven : ∀ n ∈ τ.cycleType, Even n := by
    intro n hn
    obtain ⟨i, hi⟩ := ggKGUo_mem_cycleType_minimalPeriod τ hn
    rw [← hi]
    exact hall i
  have hEvenSum : Even τ.partition.parts.sum := by
    rw [hparts]
    exact ggKGUo_multiset_even_sum halleven
  rw [Nat.Partition.parts_sum] at hEvenSum
  exact (Nat.not_even_iff_odd.mpr hcard) hEvenSum

private noncomputable def ggKGUo_basisVec {K : Type} [Field K] {r : ℕ}
    (i : HypIndex r 1) : HypIndex r 1 → K :=
  fun b => if b = i then 1 else 0

private noncomputable def ggKGUo_eigVec {K : Type} [Field K] {r : ℕ}
    (N : GL (HypIndex r 1) K) (i : HypIndex r 1) : HypIndex r 1 → K :=
  (N : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ ggKGUo_basisVec (K := K) i

private theorem ggKGUo_basisVec_ne_zero {K : Type} [Field K] {r : ℕ}
    (i : HypIndex r 1) : ggKGUo_basisVec (K := K) (r := r) i ≠ 0 := by
  intro h0
  have h1 := congrFun h0 i
  simp [ggKGUo_basisVec] at h1

private theorem ggKGUo_eigVec_ne_zero {K : Type} [Field K] {r : ℕ}
    (N : GL (HypIndex r 1) K) (i : HypIndex r 1) :
    ggKGUo_eigVec (K := K) N i ≠ 0 := by
  intro h0
  have h1 : ((N⁻¹ : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ ggKGUo_eigVec (K := K) N i = 0 := by
    rw [h0, Matrix.mulVec_zero]
  rw [ggKGUo_eigVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mulVec] at h1
  exact ggKGUo_basisVec_ne_zero (K := K) i h1

private theorem ggKGUo_eigVec_fixed {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K)
    {E : Subgroup (hypSU h r 1)} (F : ggKGUo_OddFrame (p := p) h E)
    {i : HypIndex r 1}
    (hi : ∀ x : E, F.χ x i = 1) :
    ∀ e ∈ E, e • ggKGUo_eigVec (K := K) F.N i = ggKGUo_eigVec (K := K) F.N i := by
  intro e he
  let em : Matrix (HypIndex r 1) (HypIndex r 1) K :=
    (((⟨e, he⟩ : E) : hypSU h r 1) : GL (HypIndex r 1) K)
  let u : HypIndex r 1 → K := ggKGUo_eigVec (K := K) F.N i
  have hconj := F.conj ⟨e, he⟩
  have hchi := hi ⟨e, he⟩
  change em *ᵥ u = u
  change em *ᵥ ((F.N : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ
    ggKGUo_basisVec (K := K) i) =
    (F.N : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ ggKGUo_basisVec (K := K) i
  rw [Matrix.mulVec_mulVec, hconj, ← Matrix.mulVec_mulVec]
  have hdiag : diagonal (fun b => ((F.χ ⟨e, he⟩ b : Kˣ) : K)) *ᵥ
      ggKGUo_basisVec (K := K) i = ggKGUo_basisVec (K := K) i := by
    funext b
    rw [Matrix.mulVec_diagonal]
    by_cases hb : b = i
    · subst hb; simp [ggKGUo_basisVec, hchi]
    · simp [ggKGUo_basisVec, hb]
  rw [hdiag]

private theorem ggKGUo_exists_fixed_vector {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    (E : Subgroup (hypSU h r 1)) (hE : IsElemAbelian p E) :
    ∃ u : HypIndex r 1 → K, u ≠ 0 ∧ ∀ e ∈ E, e • u = u := by
  obtain ⟨F⟩ := ggKGUo_exists_oddFrame h hp hpq E hE
  obtain ⟨τ, -, hτinv⟩ := ggKGUo_odd_exists_antisymm_perm h hpq F
  have hodd : Odd (Fintype.card (HypIndex r 1)) := by
    rw [show Fintype.card (HypIndex r 1) = 2 * r + 1 by
      simp only [HypIndex, Fintype.card_sum, Fintype.card_fin]
      omega]
    exact ⟨r, by ring⟩
  obtain ⟨i, hi⟩ := ggKGUo_exists_odd_minimalPeriod τ hodd
  have hchi : ∀ x : E, F.χ x i = 1 := fun x =>
    eq_one_of_odd_cycle τ hp hp2 (F.pow x) (hτinv x) hi
  exact ⟨ggKGUo_eigVec (K := K) F.N i, ggKGUo_eigVec_ne_zero F.N i,
    ggKGUo_eigVec_fixed h F hchi⟩

private theorem ggKGUo_hypForm_smul_smul {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (c : K) (u : HypIndex r 1 → K) :
    hypForm h r 1 (c • u) (c • u) = h.norm c * hypForm h r 1 u u := by
  simp only [hypForm_apply, Pi.smul_apply, smul_eq_mul, map_mul, UnitaryFieldData.norm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

private theorem ggKGUo_fixed_avg {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (E : Subgroup (hypSU h r 1)) [Fintype E]
    (w : HypIndex r 1 → K) :
    ∀ a ∈ E, a • (∑ e : E, e • w) = ∑ e : E, e • w := by
  classical
  intro a ha
  let aE : E := ⟨a, ha⟩
  rw [Finset.smul_sum]
  trans ∑ e : E, (aE * e) • w
  · refine Finset.sum_congr rfl fun e _ => ?_
    change a • (((e : E) : hypSU h r 1) • w) = ((aE * e : E) : hypSU h r 1) • w
    rw [smul_smul]
    rfl
  · exact Equiv.sum_comp (Equiv.mulLeft aE) (fun e : E => e • w)

private theorem ggKGUo_hypForm_avg {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (E : Subgroup (hypSU h r 1)) [Fintype E]
    (u w : HypIndex r 1 → K) (hu : ∀ e ∈ E, e • u = u) :
    hypForm h r 1 u (∑ e : E, e • w) = (Nat.card E : K) * hypForm h r 1 u w := by
  classical
  rw [map_sum]
  have hterm : ∀ e : E, hypForm h r 1 u (e • w) = hypForm h r 1 u w := by
    intro e
    have hiso := hypForm_smul_smul h ((e⁻¹ : E) : hypSU h r 1) u (e • w)
    have hu' : ((e⁻¹ : E) : hypSU h r 1) • u = u := hu _ (e⁻¹).2
    have hw' : ((e⁻¹ : E) : hypSU h r 1) • (e • w) = w := by
      change ((e⁻¹ : E) : hypSU h r 1) • (((e : E) : hypSU h r 1) • w) = w
      rw [smul_smul]
      rw [show ((e⁻¹ : E) : hypSU h r 1) * ((e : E) : hypSU h r 1) = 1 by
        exact Subtype.ext (by simp)]
      exact one_smul _ _
    rw [hu', hw'] at hiso
    exact hiso.symm
  rw [Finset.sum_congr rfl (fun e _ => hterm e), Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, nsmul_eq_mul]

private theorem ggKGUo_bar_hypForm_self {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (x : HypIndex r 1 → K) :
    h.bar (hypForm h r 1 x x) = hypForm h r 1 x x :=
  (hypForm_isSymm h).eq x x

private theorem ggKGUo_exists_norm_inv {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (x : HypIndex r 1 → K) :
    ∃ c : K, h.norm c = (hypForm h r 1 x x)⁻¹ := by
  let a : h.fixedField :=
    ⟨(hypForm h r 1 x x)⁻¹, by
      rw [UnitaryFieldData.mem_fixedField, map_inv₀, ggKGUo_bar_hypForm_self h x]⟩
  obtain ⟨c, hc⟩ := h.normHom_surjective a
  exact ⟨c, by simpa [a] using congrArg Subtype.val hc⟩

private theorem ggKGUo_exists_add_bar_eq_one {n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) : ∃ c : K, c + h.bar c = 1 := by
  obtain ⟨c, hc⟩ := exists_add_bar_eq_neg_one h
  refine ⟨c, ?_⟩
  haveI : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have htwo : (1 : K) + 1 = 0 := by
    simpa [show (2 : K) = 1 + 1 by norm_num] using h2
  have hneg : (-1 : K) = 1 := (eq_neg_of_add_eq_zero_left htwo).symm
  rwa [hneg] at hc

private theorem ggKGUo_card_ne_zero {n p : ℕ} {K : Type} [Field K]
    {E : Type*} [Group E] [Fintype E] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpg : IsPGroup p E) (h : UnitaryFieldData 2 n K) :
    (Nat.card E : K) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hpg
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd : Odd (Nat.card E) := by rw [hk]; exact hpodd.pow
  have hnot : ¬ 2 ∣ Nat.card E :=
    fun hd => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
  haveI : CharP K 2 := h.charP
  exact fun hz => hnot ((CharP.cast_eq_zero_iff K 2 (Nat.card E)).mp hz)

private theorem ggKGUo_hypForm_smul_right {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (c : K) (x y : HypIndex r 1 → K) :
    hypForm h r 1 x (c • y) = c * hypForm h r 1 x y := by
  simp only [hypForm_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

private theorem ggKGUo_hypForm_add_add {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (x y z w : HypIndex r 1 → K) :
    hypForm h r 1 (x + y) (z + w) =
      hypForm h r 1 x z + hypForm h r 1 x w +
        hypForm h r 1 y z + hypForm h r 1 y w := by
  repeat rw [hypForm_apply]
  simp only [Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]
  ring

private theorem ggKGUo_exists_fixed_norm_one {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    (E : Subgroup (hypSU h r 1)) (hE : IsElemAbelian p E) :
    ∃ v : HypIndex r 1 → K, (∀ e ∈ E, e • v = v) ∧ hypForm h r 1 v v = 1 := by
  classical
  haveI : Finite K := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype E := Fintype.ofFinite E
  have hpg : IsPGroup p E := by
    rw [isPGroup_iff_exists_pow_pow_eq_one]
    exact ⟨1, fun g => by
      apply Subtype.ext
      have := hE.2 (g : hypSU h r 1) g.2
      simpa using this⟩
  obtain ⟨u, hu_ne, hu_fix⟩ := ggKGUo_exists_fixed_vector h hp hp2 hpq E hE
  by_cases huu : hypForm h r 1 u u = 0
  · obtain ⟨w, hw⟩ : ∃ w, hypForm h r 1 u w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu_ne (hypForm_separatingLeft h u (fun y => hcon y))
    let wbar : HypIndex r 1 → K := ∑ e : E, e • w
    have hwbar_fix : ∀ e ∈ E, e • wbar = wbar := ggKGUo_fixed_avg h E w
    have hb : hypForm h r 1 u wbar ≠ 0 := by
      rw [show wbar = ∑ e : E, e • w from rfl, ggKGUo_hypForm_avg h E u w hu_fix]
      exact mul_ne_zero (ggKGUo_card_ne_zero hp hp2 hpg h) hw
    by_cases hww : hypForm h r 1 wbar wbar ≠ 0
    · obtain ⟨c, hc⟩ := ggKGUo_exists_norm_inv h wbar
      refine ⟨c • wbar, ?_, ?_⟩
      · intro e he
        rw [smul_comm, hwbar_fix e he]
      · rw [ggKGUo_hypForm_smul_smul, hc, inv_mul_cancel₀ hww]
    · have hww0 : hypForm h r 1 wbar wbar = 0 := by
        by_contra h; exact hww h
      let b : K := hypForm h r 1 u wbar
      have hb0 : b ≠ 0 := hb
      let w1 : HypIndex r 1 → K := b⁻¹ • wbar
      have hw1_fix : ∀ e ∈ E, e • w1 = w1 := by
        intro e he
        rw [show w1 = b⁻¹ • wbar from rfl, smul_comm, hwbar_fix e he]
      have hb1 : hypForm h r 1 u w1 = 1 := by
        rw
          [show w1 = b⁻¹ • wbar from rfl, ggKGUo_hypForm_smul_right, show b = hypForm h r 1 u
          wbar from rfl,
          inv_mul_cancel₀ hb0]
      have hw1w1 : hypForm h r 1 w1 w1 = 0 := by
        rw [show w1 = b⁻¹ • wbar from rfl, ggKGUo_hypForm_smul_smul, hww0, mul_zero]
      obtain ⟨c1, hc1⟩ := ggKGUo_exists_add_bar_eq_one h
      refine ⟨u + c1 • w1, ?_, ?_⟩
      · intro e he
        rw [smul_add, hu_fix e he, smul_comm, hw1_fix e he]
      · have h3 : hypForm h r 1 (c1 • w1) u = h.bar c1 := by
          rw [show hypForm h r 1 (c1 • w1) u =
            h.bar (hypForm h r 1 u (c1 • w1)) from ((hypForm_isSymm h).eq u (c1 • w1)).symm]
          rw [ggKGUo_hypForm_smul_right, hb1, mul_one]
        rw [ggKGUo_hypForm_add_add, huu, ggKGUo_hypForm_smul_right, hb1, h3,
          ggKGUo_hypForm_smul_smul, hw1w1]
        simpa using hc1
  · obtain ⟨c, hc⟩ := ggKGUo_exists_norm_inv h u
    refine ⟨c • u, ?_, ?_⟩
    · intro e he
      rw [smul_comm, hu_fix e he]
    · rw [ggKGUo_hypForm_smul_smul, hc, inv_mul_cancel₀ huu]

private theorem ggKGUo_betaHom_injective {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) : Function.Injective (ggKGUo_betaHom (r := r) h) := by
  intro g g' hgg
  apply Subtype.ext
  apply Units.ext
  have hmat : ggKGUo_betaMat (K := K) (r := r) (g : GL (HypIndex r 0) K) =
      ggKGUo_betaMat (K := K) (r := r) (g' : GL (HypIndex r 0) K) :=
    congrArg (fun z : hypSU h r 1 => ((z : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K)) hgg
  ext a b
  have := congrArg (fun M : Matrix (HypIndex r 1) (HypIndex r 1) K =>
    M (ggKGUo_oc r a) (ggKGUo_oc r b)) hmat
  simpa [ggKGUo_betaMat_apply_oc_oc] using this

private theorem ggKGUo_card_comap_beta {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (E' : Subgroup (hypSU h r 1))
    (hE' : E' ≤ (ggKGUo_betaHom (r := r) h).range) :
    Nat.card (E'.comap (ggKGUo_betaHom (r := r) h)) = Nat.card E' := by
  have hmap : (E'.comap (ggKGUo_betaHom (r := r) h)).map (ggKGUo_betaHom (r := r) h) = E' :=
    Subgroup.map_comap_eq_self hE'
  have hcard := Subgroup.card_map_of_injective (f := ggKGUo_betaHom (r := r) h)
    (ggKGUo_betaHom_injective (r := r) h) (K := E'.comap (ggKGUo_betaHom (r := r) h))
  rw [hmap] at hcard
  exact hcard.symm

private theorem ggKGUo_even_frame_transport {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    (hr : 0 < r) (E : Subgroup (hypSU h r 1)) (hE : IsElemAbelian p E)
    (hcard : p ^ r ≤ Nat.card E)
    (v : HypIndex r 1 → K) (hvfix : ∀ e ∈ E, e • v = v)
    (hv : hypForm h r 1 v v = 1) :
    ∃ (g : hypSU h r 1) (k : ℕ)
      (τ0 : (Fin k → Multiplicative (ZMod p)) →* hypSU h r 0)
      (τ : (Fin k → Multiplicative (ZMod p)) →* hypSU h r 1),
      g • v = ggKGUo_eC (K := K) (r := r) ∧
      Function.Injective τ ∧ τ.range = E ∧
      (∀ i : Fin k, ∃ w : hypSU h r 1, ∀ f, w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f)) ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ w : hypSU h r 1, ∀ f,
        w * τ f * w⁻¹ = τ (SpCoord.permAut σ f)) ∧
      Function.Injective τ0 ∧
      τ0.range = (E.map (MulAut.conj g).toMonoidHom).comap (ggKGUo_betaHom (r := r) h) ∧
      (∀ i : Fin k, ∃ w0 : hypSU h r 0, ∀ f,
        w0 * τ0 f * w0⁻¹ = τ0 (SpCoord.sgnAut i f)) ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ w0 : hypSU h r 0, ∀ f,
        w0 * τ0 f * w0⁻¹ = τ0 (SpCoord.permAut σ f)) ∧
      (∀ z0 : hypSU h r 0,
        (∀ e0 ∈ (E.map (MulAut.conj g).toMonoidHom).comap (ggKGUo_betaHom (r := r) h),
          z0 * e0 * z0⁻¹ ∈ (E.map (MulAut.conj g).toMonoidHom).comap (ggKGUo_betaHom (r := r) h)) →
        ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', z0 * τ0 f * z0⁻¹ = τ0 f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) ∧
      (∀ f, τ f = g⁻¹ * ggKGUo_beta h (τ0 f) * g) := by
  classical
  obtain ⟨g, hg⟩ := ggKGUsOdd_exists_isometry_mid h hr v hv
  have hg' : g • v = ggKGUo_eC (K := K) (r := r) := hg
  let E' : Subgroup (hypSU h r 1) := E.map (MulAut.conj g).toMonoidHom
  have hgv : g⁻¹ • ggKGUo_eC (K := K) (r := r) = v := by
    rw [← hg']
    simp
  have hE'_fix : ∀ y ∈ E', y • ggKGUo_eC (K := K) (r := r) = ggKGUo_eC (K := K) (r := r) := by
    rintro y ⟨e, he, rfl⟩
    change (g * e * g⁻¹) • ggKGUo_eC (K := K) (r := r) = ggKGUo_eC (K := K) (r := r)
    calc (g * e * g⁻¹) • ggKGUo_eC (K := K) (r := r) =
          (g * (e * g⁻¹)) • ggKGUo_eC (K := K) (r := r) := by
            exact congrArg (fun z : hypSU h r 1 => z • ggKGUo_eC (K := K) (r := r))
              (by group)
      _ = g • (e • (g⁻¹ • ggKGUo_eC (K := K) (r := r))) := by
            rw [← smul_smul, ← smul_smul]
      _ = g • (e • v) := by rw [hgv]
      _ = g • v := by rw [hvfix e he]
      _ = ggKGUo_eC (K := K) (r := r) := hg'
  have hE'_le : E' ≤ (ggKGUo_betaHom (r := r) h).range := by
    intro y hy
    exact (ggKGUo_mem_range_beta_iff (r := r) h y).mpr (hE'_fix y hy)
  let E0 : Subgroup (hypSU h r 0) := E'.comap (ggKGUo_betaHom (r := r) h)
  have hE' : IsElemAbelian p E' := IsElemAbelian.map hE (MulAut.conj g).toMonoidHom
  have hE0 : IsElemAbelian p E0 :=
    IsElemAbelian.comap hE' (ggKGUo_betaHom_injective (r := r) h)
  have hcard0 : p ^ r ≤ Nat.card E0 := by
    rw [ggKGUo_card_comap_beta (r := r) h E' hE'_le]
    rw [show Nat.card E' = Nat.card E from
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  obtain ⟨k, τ0, hτ0inj, hτ0range, hsign0, hperm0, hnorm0⟩ :=
    ggKGUs_signed_frame_hypSU h hp hp2 hpq hr E0 hE0 hcard0
  let τ : (Fin k → Multiplicative (ZMod p)) →* hypSU h r 1 :=
    (MulAut.conj g⁻¹).toMonoidHom.comp ((ggKGUo_betaHom (r := r) h).comp τ0)
  have hτapp : ∀ f, τ f = g⁻¹ * ggKGUo_beta h (τ0 f) * g := by
    intro f
    change (MulAut.conj g⁻¹) ((ggKGUo_beta h) (τ0 f)) = g⁻¹ * ggKGUo_beta h (τ0 f) * g
    rw [MulAut.conj_apply, inv_inv]
  have hτrange : τ.range = E := by
    change (((MulAut.conj g⁻¹).toMonoidHom.comp
      ((ggKGUo_betaHom (r := r) h).comp τ0)).range) = E
    rw [MonoidHom.range_comp, MonoidHom.range_comp, hτ0range]
    have hmap1 : (E0.map (ggKGUo_betaHom (r := r) h)) = E' :=
      Subgroup.map_comap_eq_self hE'_le
    rw [hmap1]
    rw [show E' = E.map (MulAut.conj g).toMonoidHom from rfl, Subgroup.map_map]
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (hypSU h r 1) := MonoidHom.ext fun x => by
      show g⁻¹ * (g * x * g⁻¹) * g = x
      group
    rw [hcomp, Subgroup.map_id]
  refine ⟨g, k, τ0, τ, hg', ?_, hτrange, ?_, ?_, hτ0inj, hτ0range, hsign0, hperm0, hnorm0, hτapp⟩
  · exact (MulAut.conj g⁻¹).injective.comp
      ((ggKGUo_betaHom_injective (r := r) h).comp hτ0inj)
  · intro i
    obtain ⟨w0, hw0⟩ := hsign0 i
    refine ⟨g⁻¹ * ggKGUo_beta h w0 * g, fun f => ?_⟩
    have hβ : ggKGUo_beta h w0 * ggKGUo_beta h (τ0 f) * (ggKGUo_beta h w0)⁻¹ =
        ggKGUo_beta h (τ0 (SpCoord.sgnAut i f)) := by
      change ggKGUo_betaHom h w0 * ggKGUo_betaHom h (τ0 f) *
        (ggKGUo_betaHom h w0)⁻¹ = ggKGUo_betaHom h (τ0 (SpCoord.sgnAut i f))
      rw [← map_mul, ← map_inv, ← map_mul, hw0 f]
    calc (g⁻¹ * ggKGUo_beta h w0 * g) * τ f * (g⁻¹ * ggKGUo_beta h w0 * g)⁻¹
        = g⁻¹ * (ggKGUo_beta h w0 * ggKGUo_beta h (τ0 f) * (ggKGUo_beta h w0)⁻¹) * g := by
          rw [hτapp f]; group
      _ = g⁻¹ * ggKGUo_beta h (τ0 (SpCoord.sgnAut i f)) * g := by rw [hβ]
      _ = τ (SpCoord.sgnAut i f) := (hτapp _).symm
  · intro σ
    obtain ⟨w0, hw0⟩ := hperm0 σ
    refine ⟨g⁻¹ * ggKGUo_beta h w0 * g, fun f => ?_⟩
    have hβ : ggKGUo_beta h w0 * ggKGUo_beta h (τ0 f) * (ggKGUo_beta h w0)⁻¹ =
        ggKGUo_beta h (τ0 (SpCoord.permAut σ f)) := by
      change ggKGUo_betaHom h w0 * ggKGUo_betaHom h (τ0 f) *
        (ggKGUo_betaHom h w0)⁻¹ = ggKGUo_betaHom h (τ0 (SpCoord.permAut σ f))
      rw [← map_mul, ← map_inv, ← map_mul, hw0 f]
    calc (g⁻¹ * ggKGUo_beta h w0 * g) * τ f * (g⁻¹ * ggKGUo_beta h w0 * g)⁻¹
        = g⁻¹ * (ggKGUo_beta h w0 * ggKGUo_beta h (τ0 f) * (ggKGUo_beta h w0)⁻¹) * g := by
          rw [hτapp f]; group
      _ = g⁻¹ * ggKGUo_beta h (τ0 (SpCoord.permAut σ f)) * g := by rw [hβ]
      _ = τ (SpCoord.permAut σ f) := (hτapp _).symm

private theorem ggKGUo_even_fixed_zero {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    (E0 : Subgroup (hypSU h r 0)) (hE0 : IsElemAbelian p E0)
    (hcard0 : p ^ r ≤ Nat.card E0) :
    ∀ w : HypIndex r 0 → K, (∀ e ∈ E0, e • w = w) → w = 0 := by
  classical
  obtain ⟨F⟩ := nonempty_hypEigenframe h hp hpq E0 hE0
  obtain ⟨τ, hτpos, hτinv⟩ := F.exists_antisymm_perm hpq
  have hEmap : Nat.card E0 = Nat.card F.χ.range :=
    Nat.card_congr (MonoidHom.ofInjective F.inj).toEquiv
  have hcardχ : p ^ r ≤ Nat.card F.χ.range := by rwa [← hEmap]
  have hpow : ∀ t ∈ F.χ.range, ∀ i, t i ^ p = 1 := by
    rintro t ⟨x, rfl⟩ i; exact F.pow x i
  have hτ : ∀ t ∈ F.χ.range, ∀ i, t (τ i) = (t i)⁻¹ := by
    rintro t ⟨x, rfl⟩ i; exact hτinv x i
  have hcardι : Fintype.card (HypIndex r 0) = 2 * r := by
    simp only [HypIndex, Fintype.card_sum, Fintype.card_fin]; omega
  obtain ⟨hτ1, hτ2, hW⟩ :=
    fpf_involution_of_card_ge hp hp2 hcardι τ F.χ.range hpow hτ hcardχ
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  let u : Kˣ := (hζ.isUnit hp.ne_zero).unit
  have hu : orderOf u = p :=
    (IsPrimitiveRoot.isUnit_unit (n := p) hp.ne_zero hζ).eq_orderOf.symm
  have hex : ∀ i : HypIndex r 0, ∃ x : E0, F.χ x i ≠ 1 := by
    intro i
    obtain ⟨t, htpow, htsymm, htii⟩ :=
      exists_mem_of_fpf_involution hp hp2 hu τ hτ1 hτ2 i i (hτ1 i).symm
    obtain ⟨x, hx⟩ := hW t htpow htsymm
    refine ⟨x, ?_⟩
    rw [hx]
    intro hti
    exact htii (by simp [hti])
  intro w hw
  let N : Matrix (HypIndex r 0) (HypIndex r 0) K := (F.N : Matrix _ _ K)
  let c : HypIndex r 0 → K := ((F.N⁻¹ : GL (HypIndex r 0) K) :
    Matrix (HypIndex r 0) (HypIndex r 0) K) *ᵥ w
  have hwN : w = N *ᵥ c := by
    rw [show w = (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K) *ᵥ
      (((F.N⁻¹ : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) *ᵥ w) by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]]
  have hci : ∀ i, c i = 0 := by
    intro i
    obtain ⟨x, hxi⟩ := hex i
    have hxw : (((x : E0) : hypSU h r 0) : GL (HypIndex r 0) K) • w = w := hw _ x.2
    have hdiag : diagonal (fun b => ((F.χ x b : Kˣ) : K)) *ᵥ c = c := by
      have hconj := F.conj x
      have hstep : ((x : E0) : GL (HypIndex r 0) K) *
          (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K) =
          (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K) *
            diagonal (fun b => ((F.χ x b : Kˣ) : K)) := hconj
      have h1 : (((x : E0) : GL (HypIndex r 0) K) :
          Matrix (HypIndex r 0) (HypIndex r 0) K) *ᵥ (N *ᵥ c) = N *ᵥ c := by
        rw [← hwN]; exact hxw
      have h2 : (((x : E0) : GL (HypIndex r 0) K) :
          Matrix (HypIndex r 0) (HypIndex r 0) K) *ᵥ (N *ᵥ c) =
          N *ᵥ (diagonal (fun b => ((F.χ x b : Kˣ) : K)) *ᵥ c) := by
        calc (((x : E0) : GL (HypIndex r 0) K) :
              Matrix (HypIndex r 0) (HypIndex r 0) K) *ᵥ (N *ᵥ c)
            = ((((x : E0) : GL (HypIndex r 0) K) :
                Matrix (HypIndex r 0) (HypIndex r 0) K) * N) *ᵥ c := by
                rw [← Matrix.mulVec_mulVec]
          _ = (N * diagonal (fun b => ((F.χ x b : Kˣ) : K))) *ᵥ c := by rw [hstep]
          _ = N *ᵥ (diagonal (fun b => ((F.χ x b : Kˣ) : K)) *ᵥ c) := by
                rw [← Matrix.mulVec_mulVec]
      have hNc : N *ᵥ (diagonal (fun b => ((F.χ x b : Kˣ) : K)) *ᵥ c) = N *ᵥ c :=
        h2.symm.trans h1
      have hinj : Function.Injective (fun v : HypIndex r 0 → K => N *ᵥ v) := by
        intro a b hab
        have hh := congrArg (fun v => ((F.N⁻¹ : GL (HypIndex r 0) K) :
          Matrix (HypIndex r 0) (HypIndex r 0) K) *ᵥ v) hab
        simpa [N, Matrix.mulVec_mulVec] using hh
      exact hinj hNc
    have hentry := congrFun hdiag i
    rw [Matrix.mulVec_diagonal] at hentry
    by_cases hc0 : c i = 0
    · exact hc0
    · exfalso
      have h1 : ((F.χ x i : Kˣ) : K) = 1 := by
        rw [mul_comm] at hentry
        exact mul_left_cancel₀ hc0 (by simpa using hentry)
      apply hxi
      exact Units.ext h1
  have hc0 : c = 0 := by funext i; exact hci i
  rw [hwN, hc0, Matrix.mulVec_zero]

private theorem ggKGUo_betaMat_mulVec {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g0 : hypSU h r 0) (x : HypIndex r 1 → K) :
    ggKGUo_betaMat (K := K) (g0 : GL (HypIndex r 0) K) *ᵥ x =
      fun a => match ggKGUo_osplit r a with
        | Sum.inl b => (((g0 : GL (HypIndex r 0) K) :
            Matrix (HypIndex r 0) (HypIndex r 0) K) *ᵥ
              (fun b => x (ggKGUo_oc r b))) b
        | Sum.inr _ => x (ggKGUo_c r) := by
  funext a
  rcases a with i | k | i
  · simp [ggKGUo_betaMat, ggKGUo_betaMatOfMat, Matrix.mulVec, dotProduct,
      Matrix.reindex_apply, Matrix.submatrix_apply, ggKGUo_osplit, ggKGUo_oc, ggKGUo_c]
  · fin_cases k
    simp [ggKGUo_betaMat, ggKGUo_betaMatOfMat, Matrix.mulVec, dotProduct,
      Matrix.reindex_apply, Matrix.submatrix_apply, ggKGUo_osplit, ggKGUo_oc, ggKGUo_c]
  · simp [ggKGUo_betaMat, ggKGUo_betaMatOfMat, Matrix.mulVec, dotProduct,
      Matrix.reindex_apply, Matrix.submatrix_apply, ggKGUo_osplit, ggKGUo_oc, ggKGUo_c]

private theorem ggKGUo_oc_part_fixed {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g0 : hypSU h r 0) (x : HypIndex r 1 → K)
    (hfix : ggKGUo_beta h g0 • x = x) :
    (((g0 : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) *ᵥ
      (fun b => x (ggKGUo_oc r b))) = fun b => x (ggKGUo_oc r b) := by
  have hmat := ggKGUo_betaMat_mulVec h g0 x
  have hfun : ggKGUo_beta h g0 • x = ggKGUo_betaMat (K := K) (g0 : GL (HypIndex r 0) K) *ᵥ x := rfl
  rw [hfun] at hfix
  rw [hmat] at hfix
  funext b
  have hb := congrFun hfix (ggKGUo_oc r b)
  simpa [ggKGUo_osplit_apply_oc] using hb

private theorem ggKGUo_fixed_space {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    (E0 : Subgroup (hypSU h r 0)) (hE0 : IsElemAbelian p E0)
    (hcard0 : p ^ r ≤ Nat.card E0) (x : HypIndex r 1 → K)
    (hx : ∀ e0 ∈ E0, ggKGUo_beta h e0 • x = x) :
    x = x (ggKGUo_c r) • ggKGUo_eC (K := K) (r := r) := by
  have h0 : (fun b => x (ggKGUo_oc r b)) = 0 := by
    apply ggKGUo_even_fixed_zero h hp hp2 hpq E0 hE0 hcard0
    intro e0 he0
    show (((e0 : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) *ᵥ
      (fun b => x (ggKGUo_oc r b))) = fun b => x (ggKGUo_oc r b)
    exact ggKGUo_oc_part_fixed h e0 x (hx e0 he0)
  funext a
  rcases a with i | k | i
  · have hthis : x (Sum.inl i) = 0 := congrFun h0 (Sum.inl i)
    rw [hthis]
    simp [ggKGUo_eC, ggKGUo_c]
  · fin_cases k
    simp [ggKGUo_eC, ggKGUo_c]
  · have hthis : x (Sum.inr (Sum.inr i)) = 0 := congrFun h0 (Sum.inr (Sum.inr i))
    rw [hthis]
    simp [ggKGUo_eC, ggKGUo_c]

private theorem ggKGUo_eC_norm {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) :
    hypForm h r 1 (ggKGUo_eC (K := K) (r := r)) (ggKGUo_eC (K := K) (r := r)) = 1 := by
  rw [hypForm_apply]
  rw [Finset.sum_eq_single (ggKGUo_c r)]
  · rw [ggKGUo_eC, Pi.single_eq_same, map_one, one_mul, ggKGUo_hypPartner_c,
      Pi.single_eq_same]
  · intro b _ hb
    rw [ggKGUo_eC, Pi.single_eq_of_ne hb, map_zero, zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ (ggKGUo_c r)) hc

private theorem ggKGUo_eC_ne_zero {K : Type} [Field K] {r : ℕ} :
    ggKGUo_eC (K := K) (r := r) ≠ 0 := by
  intro h0
  have h1 := congrFun h0 (ggKGUo_c r)
  rw [ggKGUo_eC, Pi.single_eq_same] at h1
  exact one_ne_zero h1

private theorem ggKGUo_normalizer_scalar {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    (E0 : Subgroup (hypSU h r 0)) (hE0 : IsElemAbelian p E0)
    (hcard0 : p ^ r ≤ Nat.card E0) (g' : hypSU h r 1)
    (hnorm_inv : ∀ e ∈ E0.map (ggKGUo_betaHom (r := r) h),
      g'⁻¹ * e * g' ∈ E0.map (ggKGUo_betaHom (r := r) h)) :
    ∃ lam : K, lam ≠ 0 ∧ h.norm lam = 1 ∧
      g' • ggKGUo_eC (K := K) (r := r) = lam • ggKGUo_eC (K := K) (r := r) := by
  have hfix : ∀ e ∈ E0, ggKGUo_beta h e •
      (g' • ggKGUo_eC (K := K) (r := r)) = g' • ggKGUo_eC (K := K) (r := r) := by
    intro e he
    have hmemE : ggKGUo_beta h e ∈ E0.map (ggKGUo_betaHom (r := r) h) :=
      Subgroup.mem_map.mpr ⟨e, he, rfl⟩
    obtain ⟨e1, he1, heq⟩ := hnorm_inv (ggKGUo_beta h e) hmemE
    have hfixe : ggKGUo_beta h e1 • ggKGUo_eC (K := K) (r := r) =
        ggKGUo_eC (K := K) (r := r) := ggKGUo_beta_smul_c h e1
    calc ggKGUo_beta h e • (g' • ggKGUo_eC (K := K) (r := r))
        = (ggKGUo_beta h e * g') • ggKGUo_eC (K := K) (r := r) :=
          (mul_smul _ _ _).symm
      _ = (g' * (g'⁻¹ * ggKGUo_beta h e * g')) • ggKGUo_eC (K := K) (r := r) :=
          congrArg (· • ggKGUo_eC (K := K) (r := r)) (by group)
      _ = g' • ((g'⁻¹ * ggKGUo_beta h e * g') • ggKGUo_eC (K := K) (r := r)) :=
          mul_smul _ _ _
      _ = g' • (ggKGUo_beta h e1 • ggKGUo_eC (K := K) (r := r)) := by rw [← heq]; rfl
      _ = g' • ggKGUo_eC (K := K) (r := r) := by rw [hfixe]
  have hdec := ggKGUo_fixed_space h hp hp2 hpq E0 hE0 hcard0
    (g' • ggKGUo_eC (K := K) (r := r)) hfix
  refine ⟨(g' • ggKGUo_eC (K := K) (r := r)) (ggKGUo_c r), ?_, ?_, hdec⟩
  · have hiso := hypForm_smul_smul h g' (ggKGUo_eC (K := K) (r := r))
      (ggKGUo_eC (K := K) (r := r))
    rw [ggKGUo_eC_norm h] at hiso
    rw [hdec, ggKGUo_hypForm_smul_smul, ggKGUo_eC_norm h, mul_one] at hiso
    intro h0
    rw [h0] at hiso
    simp [UnitaryFieldData.norm] at hiso
  · have hiso := hypForm_smul_smul h g' (ggKGUo_eC (K := K) (r := r))
      (ggKGUo_eC (K := K) (r := r))
    rw [ggKGUo_eC_norm h] at hiso
    rw [hdec, ggKGUo_hypForm_smul_smul, ggKGUo_eC_norm h, mul_one] at hiso
    exact hiso

private theorem ggKGUo_betaMatOfMat_diagonal {K : Type} [Field K] {r : ℕ}
    (e : HypIndex r 0 → K) :
    ggKGUo_betaMatOfMat (K := K) (diagonal e) =
      diagonal (Sum.elim e (fun _ => (1 : K)) ∘ ggKGUo_osplit r) := by
  rw [ggKGUo_betaMatOfMat]
  rw [show (1 : Matrix Unit Unit K) = diagonal (fun _ => (1 : K)) from
    Matrix.diagonal_one.symm]
  rw [Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Equiv.symm_symm,
    Matrix.submatrix_diagonal_equiv]

private theorem ggKGUo_betaMat_diagonal {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (g : hypSU h r 0) (e : HypIndex r 0 → K)
    (hg : (((g : hypSU h r 0) : GL (HypIndex r 0) K) :
      Matrix (HypIndex r 0) (HypIndex r 0) K) = diagonal e) :
    ggKGUo_betaMat (K := K) (g : GL (HypIndex r 0) K) =
      diagonal (Sum.elim e (fun _ => (1 : K)) ∘ ggKGUo_osplit r) := by
  rw [ggKGUo_betaMat, hg, ggKGUo_betaMatOfMat_diagonal]

private theorem ggKGUo_diag_corr {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) {ζ : K} (hr : 0 < r) {lam : K} (hlam : h.norm lam = 1)
    (ι : (Fin r → Multiplicative (ZMod p)) →* hypSU h r 0)
    (hι : ∀ t : Fin r → ZMod p,
      (((ι (Multiplicative.ofAdd t) : hypSU h r 0) : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) = diagonal (hypEntries ζ t)) :
    ∃ C : hypSU h r 1, C • ggKGUo_eC (K := K) (r := r) =
        lam⁻¹ • ggKGUo_eC (K := K) (r := r) ∧
      ∀ t : Fin r → ZMod p,
        C * ggKGUo_beta h (ι (Multiplicative.ofAdd t)) =
          ggKGUo_beta h (ι (Multiplicative.ofAdd t)) * C := by
  classical
  have hlam0 : lam ≠ 0 := by
    intro h0
    have hz : h.norm lam = 0 := by rw [h0]; simp [UnitaryFieldData.norm]
    rw [hlam] at hz
    exact one_ne_zero hz
  obtain ⟨a, ha0, ha⟩ := h.exists_div_bar_eq hlam
  let i0 : Fin r := ⟨0, hr⟩
  let a' : Fin r → Kˣ := Function.update (fun _ => 1) i0 (Units.mk0 a ha0)
  let d : Fin 1 → Kˣ := fun _ => Units.mk0 lam⁻¹ (inv_ne_zero hlam0)
  have hd : ∀ k : Fin 1, h.norm (d k) = 1 := by
    intro k
    simp only [d, Units.val_mk0, UnitaryFieldData.norm, map_inv₀]
    rw [← mul_inv, show lam * h.bar lam = h.norm lam from rfl, hlam, inv_one]

  have hratio : torusRatio h a' d = 1 := by
    rw [torusRatio]
    have hprod : (∏ i, ((a' i : K) / h.bar (a' i))) = a / h.bar a := by
      rw [Fintype.prod_eq_single i0]
      · simp [a', i0]
      · intro j hj
        simp [a', Function.update_of_ne hj]
    rw [hprod, ha]
    simp only [d, Units.val_mk0, Finset.univ_unique, Finset.prod_singleton]
    exact mul_inv_cancel₀ hlam0
  obtain ⟨C, hCmem, hCmat⟩ := torusMat_mem_hypSU (d := d) h a' hd hratio
  refine ⟨C, ?_, ?_⟩
  · change (((C : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ
      ggKGUo_eC (K := K) (r := r)) = lam⁻¹ • ggKGUo_eC (K := K) (r := r)
    rw [hCmat, ggKGUo_eC, Matrix.diagonal_mulVec_single]
    funext a
    by_cases ha : a = ggKGUo_c r
    · subst ha
      rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      simp [ggKGUo_c, torusEntries, d]
    · simp [Pi.single_eq_of_ne ha]
  · intro t
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hCmat]
    rw [show (((ggKGUo_beta h (ι (Multiplicative.ofAdd t)) : hypSU h r 1) :
        GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      ggKGUo_betaMat (K := K) (ι (Multiplicative.ofAdd t) : GL (HypIndex r 0) K) from rfl]
    rw [ggKGUo_betaMat_diagonal h (ι (Multiplicative.ofAdd t)) (hypEntries ζ t) (hι t)]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    exact mul_comm _ _


private theorem ggKGUo_conj_comm {G : Type*} [Group G] (a b C x : G)
    (hx : x = a⁻¹ * b * a) (hC : C * b = b * C) :
    (a⁻¹ * C * a) * x = x * (a⁻¹ * C * a) := by
  subst hx
  calc (a⁻¹ * C * a) * (a⁻¹ * b * a) = a⁻¹ * (C * b) * a := by group
    _ = a⁻¹ * (b * C) * a := by rw [hC]
    _ = (a⁻¹ * b * a) * (a⁻¹ * C * a) := by group

private theorem ggKGUo_hypSU_smul_smul {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (y : hypSU h r 1) (c : K) (v : HypIndex r 1 → K) :
    y • (c • v) = c • (y • v) := by
  change (((y : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ
      (c • v)) = c • (((y : GL (HypIndex r 1) K) :
        Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ v)
  rw [Matrix.mulVec_smul]

private theorem ggKGUo_exists_centralizing_corr {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    (hr : 0 < r) (E0 : Subgroup (hypSU h r 0)) (hE0 : IsElemAbelian p E0)
    (hcard0 : p ^ r ≤ Nat.card E0) {lam : K} (hlam : h.norm lam = 1) :
    ∃ c' : hypSU h r 1,
      (∀ e0 ∈ E0, c' * ggKGUo_beta h e0 = ggKGUo_beta h e0 * c') ∧
      c' • ggKGUo_eC (K := K) (r := r) = lam⁻¹ • ggKGUo_eC (K := K) (r := r) := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  have hbar : h.bar ζ = ζ := bar_eq_self_of_pow_eq_one h hpq hζ.pow_eq_one
  obtain ⟨ι, hι⟩ := exists_hypTorusHom (r := r) h hp hζ hbar
  obtain ⟨g0, hg0⟩ := exists_conj_hypEntries h hp hp2 hpq hζ hr E0 hE0 hcard0
  have hle : E0.map (MulAut.conj g0).toMonoidHom ≤ ι.range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := hg0 x hx
    refine ⟨Multiplicative.ofAdd t, Subtype.ext (Units.ext ?_)⟩
    rw [hι t]
    exact ht.symm
  have hcardmap : Nat.card (E0.map (MulAut.conj g0).toMonoidHom) = Nat.card E0 :=
    Subgroup.card_map_of_injective (MulAut.conj g0).injective
  have heq : E0.map (MulAut.conj g0).toMonoidHom = ι.range :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [hcardmap, card_range_hypTorusHom h hp hζ ι hι]
      exact hcard0)
  obtain ⟨C, hCeC, hCcomm⟩ := ggKGUo_diag_corr h hr hlam ι hι
  refine ⟨(ggKGUo_beta h g0)⁻¹ * C * ggKGUo_beta h g0, ?_, ?_⟩
  · intro e0 he0
    have hmem : MulAut.conj g0 e0 ∈ ι.range := by
      rw [← heq]
      exact Subgroup.mem_map.mpr ⟨e0, he0, rfl⟩
    obtain ⟨t, ht⟩ := hmem
    have ht' : ggKGUo_beta h (ι t) =
        ggKGUo_beta h g0 * ggKGUo_beta h e0 * (ggKGUo_beta h g0)⁻¹ := by
      rw [ht]
      change ggKGUo_betaHom h (g0 * e0 * g0⁻¹) =
        ggKGUo_betaHom h g0 * ggKGUo_betaHom h e0 * (ggKGUo_betaHom h g0)⁻¹
      rw [map_mul, map_mul, map_inv]
    have hx : ggKGUo_beta h e0 =
        (ggKGUo_beta h g0)⁻¹ * ggKGUo_beta h (ι t) * ggKGUo_beta h g0 := by
      rw [ht']; group
    have hC' : C * ggKGUo_beta h (ι t) = ggKGUo_beta h (ι t) * C := by
      rw [← ofAdd_toAdd t]
      exact hCcomm (Multiplicative.toAdd t)
    exact ggKGUo_conj_comm (ggKGUo_beta h g0) (ggKGUo_beta h (ι t)) C
      (ggKGUo_beta h e0) hx hC'
  · calc ((ggKGUo_beta h g0)⁻¹ * C * ggKGUo_beta h g0) • ggKGUo_eC (K := K) (r := r)
        = (ggKGUo_beta h g0)⁻¹ • (C • (ggKGUo_beta h g0 • ggKGUo_eC (K := K) (r := r))) := by
          rw [mul_smul, mul_smul]
      _ = (ggKGUo_beta h g0)⁻¹ • (C • ggKGUo_eC (K := K) (r := r)) := by
          rw [ggKGUo_beta_smul_c h g0]
      _ = (ggKGUo_beta h g0)⁻¹ • (lam⁻¹ • ggKGUo_eC (K := K) (r := r)) := by rw [hCeC]
      _ = lam⁻¹ • ((ggKGUo_beta h g0)⁻¹ • ggKGUo_eC (K := K) (r := r)) := by
          rw [ggKGUo_hypSU_smul_smul]
      _ = lam⁻¹ • ggKGUo_eC (K := K) (r := r) := by
          rw [show (ggKGUo_beta h g0)⁻¹ = ggKGUo_beta h g0⁻¹ from
            (map_inv (ggKGUo_betaHom h) g0).symm, ggKGUo_beta_smul_c h g0⁻¹]


theorem ggKGUs_signed_frame_hypSU_odd {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    (hr : 0 < r) (E : Subgroup (hypSU h r 1)) (hE : IsElemAbelian p E)
    (hcard : p ^ r ≤ Nat.card E) :
    ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* hypSU h r 1), Function.Injective τ ∧
      τ.range = E ∧
      (∀ i : Fin k, ∃ w : hypSU h r 1, ∀ f, w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f)) ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ w : hypSU h r 1, ∀ f,
        w * τ f * w⁻¹ = τ (SpCoord.permAut σ f)) ∧
      ∀ g : hypSU h r 1, (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
        ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
  classical
  obtain ⟨v, hvfix, hvnorm⟩ := ggKGUo_exists_fixed_norm_one h hp hp2 hpq E hE
  obtain ⟨g, k, τ0, τ, hgv, hτinj, hτrange, hsign, hperm, hτ0inj, hτ0range, hsign0, hperm0,
    hnorm0, hτapp⟩ :=
    ggKGUo_even_frame_transport h hp hp2 hpq hr E hE hcard v hvfix hvnorm
  refine ⟨k, τ, hτinj, hτrange, hsign, hperm, fun n hn => ?_⟩
  let E' : Subgroup (hypSU h r 1) := E.map (MulAut.conj g).toMonoidHom
  let E0 : Subgroup (hypSU h r 0) :=
    (E.map (MulAut.conj g).toMonoidHom).comap (ggKGUo_betaHom (r := r) h)
  have hgv_inv : g⁻¹ • ggKGUo_eC (K := K) (r := r) = v := by
    rw [← hgv]; simp
  have hE'_le : E' ≤ (ggKGUo_betaHom (r := r) h).range := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := hy
    refine (ggKGUo_mem_range_beta_iff (r := r) h _).mpr ?_
    change (g * e * g⁻¹) • ggKGUo_eC (K := K) (r := r) = ggKGUo_eC (K := K) (r := r)
    calc (g * e * g⁻¹) • ggKGUo_eC (K := K) (r := r)
        = g • (e • (g⁻¹ • ggKGUo_eC (K := K) (r := r))) := by rw [mul_smul, mul_smul]
      _ = g • (e • v) := by rw [hgv_inv]
      _ = g • v := by rw [hvfix e he]
      _ = ggKGUo_eC (K := K) (r := r) := hgv
  have hE0map : E0.map (ggKGUo_betaHom (r := r) h) = E' :=
    Subgroup.map_comap_eq_self hE'_le
  have hE' : IsElemAbelian p E' := IsElemAbelian.map hE (MulAut.conj g).toMonoidHom
  have hE0 : IsElemAbelian p E0 := IsElemAbelian.comap hE' (ggKGUo_betaHom_injective (r := r) h)
  have hcard0 : p ^ r ≤ Nat.card E0 := by
    have h1 : Nat.card E0 = Nat.card E' := ggKGUo_card_comap_beta (r := r) h E' hE'_le
    rw [h1]
    rw [show Nat.card E' = Nat.card E from
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  let g' : hypSU h r 1 := g * n * g⁻¹
  have hnorm : ∀ e ∈ E', g' * e * g'⁻¹ ∈ E' := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := he
    refine Subgroup.mem_map.mpr ⟨n * e0 * n⁻¹, hn e0 he0, ?_⟩
    change g * (n * e0 * n⁻¹) * g⁻¹ = g' * (g * e0 * g⁻¹) * g'⁻¹
    rw [show g' = g * n * g⁻¹ from rfl]
    group
  have hnorm' : ∀ e ∈ E0.map (ggKGUo_betaHom (r := r) h),
      g' * e * g'⁻¹ ∈ E0.map (ggKGUo_betaHom (r := r) h) := by
    intro e he
    rw [hE0map] at he ⊢
    exact hnorm e he
  have hnorm_inv : ∀ e ∈ E', g'⁻¹ * e * g' ∈ E' := by
    have hle : E'.map (MulAut.conj g').toMonoidHom ≤ E' := by
      rintro y ⟨x, hx, rfl⟩
      exact hnorm x hx
    have heq : E'.map (MulAut.conj g').toMonoidHom = E' :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective (f := (MulAut.conj g').toMonoidHom)
          (fun _ _ hab => (MulAut.conj g').injective hab) (K := E')])
    intro e he
    have hmem : e ∈ E'.map (MulAut.conj g').toMonoidHom := by rw [heq]; exact he
    obtain ⟨x, hx, hxeq⟩ := hmem
    have hx' : g'⁻¹ * e * g' = x := by
      rw [← hxeq]
      change g'⁻¹ * (g' * x * g'⁻¹) * g' = x
      group
    rw [hx']
    exact hx
  have hnorm_inv' : ∀ e ∈ E0.map (ggKGUo_betaHom (r := r) h),
      g'⁻¹ * e * g' ∈ E0.map (ggKGUo_betaHom (r := r) h) := by
    intro e he
    rw [hE0map] at he ⊢
    exact hnorm_inv e he
  obtain ⟨lam, hlam0, hlamnorm, hg'eC⟩ :=
    ggKGUo_normalizer_scalar h hp hp2 hpq E0 hE0 hcard0 g' hnorm_inv'
  obtain ⟨c', hc'comm, hc'eC⟩ :=
    ggKGUo_exists_centralizing_corr h hp hp2 hpq hr E0 hE0 hcard0 hlamnorm
  let z : hypSU h r 1 := g' * c'
  have hzfix : z • ggKGUo_eC (K := K) (r := r) = ggKGUo_eC (K := K) (r := r) := by
    change (g' * c') • ggKGUo_eC (K := K) (r := r) = ggKGUo_eC (K := K) (r := r)
    calc (g' * c') • ggKGUo_eC (K := K) (r := r)
        = g' • (c' • ggKGUo_eC (K := K) (r := r)) := mul_smul _ _ _
      _ = g' • (lam⁻¹ • ggKGUo_eC (K := K) (r := r)) := by rw [hc'eC]
      _ = lam⁻¹ • (g' • ggKGUo_eC (K := K) (r := r)) :=
          ggKGUo_hypSU_smul_smul h g' lam⁻¹ (ggKGUo_eC (K := K) (r := r))
      _ = lam⁻¹ • (lam • ggKGUo_eC (K := K) (r := r)) := by rw [hg'eC]
      _ = (lam⁻¹ * lam) • ggKGUo_eC (K := K) (r := r) := smul_smul _ _ _
      _ = ggKGUo_eC (K := K) (r := r) := by rw [inv_mul_cancel₀ hlam0, one_smul]
  obtain ⟨z0, hz0⟩ := (ggKGUo_mem_range_beta_iff (r := r) h z).mpr hzfix
  have hnormz0 : ∀ e0 ∈ E0, z0 * e0 * z0⁻¹ ∈ E0 := by
    intro e0 he0
    change z0 * e0 * z0⁻¹ ∈ E'.comap (ggKGUo_betaHom (r := r) h)
    rw [Subgroup.mem_comap]
    have hβeq2 : ggKGUo_betaHom h (z0 * e0 * z0⁻¹)
        = g' * ggKGUo_betaHom h e0 * g'⁻¹ := by
      have hstep : ggKGUo_betaHom h (z0 * e0 * z0⁻¹)
          = ggKGUo_betaHom h z0 * ggKGUo_betaHom h e0 * (ggKGUo_betaHom h z0)⁻¹ := by
        calc ggKGUo_betaHom h (z0 * e0 * z0⁻¹)
            = ggKGUo_betaHom h (z0 * e0) * ggKGUo_betaHom h (z0⁻¹) := map_mul _ _ _
          _ = (ggKGUo_betaHom h z0 * ggKGUo_betaHom h e0) * ggKGUo_betaHom h (z0⁻¹) := by
                rw [map_mul]
          _ = (ggKGUo_betaHom h z0 * ggKGUo_betaHom h e0) * (ggKGUo_betaHom h z0)⁻¹ := by
                rw [map_inv]
          _ = ggKGUo_betaHom h z0 * ggKGUo_betaHom h e0 *
                (ggKGUo_betaHom h z0)⁻¹ := rfl
      rw [hstep, hz0]
      calc z * ggKGUo_betaHom h e0 * z⁻¹
          = (g' * c') * ggKGUo_betaHom h e0 * (g' * c')⁻¹ := rfl
        _ = g' * (c' * ggKGUo_betaHom h e0) * c'⁻¹ * g'⁻¹ := by group
        _ = g' * (ggKGUo_betaHom h e0 * c') * c'⁻¹ * g'⁻¹ := by
              change g' * (c' * ggKGUo_beta h e0) * c'⁻¹ * g'⁻¹
                = g' * (ggKGUo_beta h e0 * c') * c'⁻¹ * g'⁻¹
              rw [hc'comm e0 he0]
        _ = g' * ggKGUo_betaHom h e0 * g'⁻¹ := by group
    rw [hβeq2]
    exact hnorm (ggKGUo_betaHom h e0) (by
      change e0 ∈ E'.comap (ggKGUo_betaHom h)
      exact he0)
  obtain ⟨π, ε, hε, hrel⟩ := hnorm0 z0 hnormz0
  refine ⟨π, ε, hε, ?_⟩
  intro f f' hff' i
  have h1 := congrArg (fun w : hypSU h r 1 => g * w * g⁻¹) hff'
  rw [hτapp f, hτapp f'] at h1
  have hβeq : g' * ggKGUo_betaHom h (τ0 f) * g'⁻¹ = ggKGUo_betaHom h (τ0 f') := by
    calc g' * ggKGUo_betaHom h (τ0 f) * g'⁻¹
        = g * (n * (g⁻¹ * ggKGUo_betaHom h (τ0 f) * g) * n⁻¹) * g⁻¹ := by
          rw [show g' = g * n * g⁻¹ from rfl]; group
      _ = g * (g⁻¹ * ggKGUo_betaHom h (τ0 f') * g) * g⁻¹ := h1
      _ = ggKGUo_betaHom h (τ0 f') := by group
  have hz0eq : ggKGUo_betaHom h (z0 * τ0 f * z0⁻¹)
      = g' * ggKGUo_betaHom h (τ0 f) * g'⁻¹ := by
    have hmem : τ0 f ∈ E0 := by
      change τ0 f ∈ Subgroup.comap (ggKGUo_betaHom h)
        (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) E)
      rw [← hτ0range]
      exact ⟨f, rfl⟩
    have hstep : ggKGUo_betaHom h (z0 * τ0 f * z0⁻¹)
        = ggKGUo_betaHom h z0 * ggKGUo_betaHom h (τ0 f) *
            (ggKGUo_betaHom h z0)⁻¹ := by
      calc ggKGUo_betaHom h (z0 * τ0 f * z0⁻¹)
          = ggKGUo_betaHom h (z0 * τ0 f) * ggKGUo_betaHom h (z0⁻¹) := map_mul _ _ _
        _ = (ggKGUo_betaHom h z0 * ggKGUo_betaHom h (τ0 f)) *
              ggKGUo_betaHom h (z0⁻¹) := by rw [map_mul]
        _ = (ggKGUo_betaHom h z0 * ggKGUo_betaHom h (τ0 f)) *
              (ggKGUo_betaHom h z0)⁻¹ := by rw [map_inv]
        _ = ggKGUo_betaHom h z0 * ggKGUo_betaHom h (τ0 f) *
              (ggKGUo_betaHom h z0)⁻¹ := rfl
    rw [hstep, hz0]
    calc z * ggKGUo_betaHom h (τ0 f) * z⁻¹
        = (g' * c') * ggKGUo_betaHom h (τ0 f) * (g' * c')⁻¹ := rfl
      _ = g' * (c' * ggKGUo_betaHom h (τ0 f)) * c'⁻¹ * g'⁻¹ := by group
      _ = g' * (ggKGUo_betaHom h (τ0 f) * c') * c'⁻¹ * g'⁻¹ := by
            change g' * (c' * ggKGUo_beta h (τ0 f)) * c'⁻¹ * g'⁻¹
              = g' * (ggKGUo_beta h (τ0 f) * c') * c'⁻¹ * g'⁻¹
            rw [hc'comm (τ0 f) hmem]
      _ = g' * ggKGUo_betaHom h (τ0 f) * g'⁻¹ := by group
  exact hrel f f' ((ggKGUo_betaHom_injective (r := r) h) (by rw [hz0eq, hβeq])) i

end CFSG.StandardType

end
