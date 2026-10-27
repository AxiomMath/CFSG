module

public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSUBasis
public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSL
public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSURoot

public section

namespace CFSG.StandardType

open Matrix Module CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

section Adapted

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem exists_ggU_adapted_family (hσ : IsUnitaryInvolution σ) {N : Matrix (Fin n) (Fin n) F}
    (hN : N * N = 0) (hadj : ∀ x y, ggUForm σ (N *ᵥ x) y = ggUForm σ x (N *ᵥ y)) :
    ∃ l : ℕ, 2 * l ≤ n ∧ l = finrank F (LinearMap.range N.mulVecLin) ∧
      ∃ f : Fin n → (Fin n → F),
        (∀ i j, ggUForm σ (f i) (f j) = if j = Fin.rev i then 1 else 0) ∧
        ∀ j, N *ᵥ f j = if (j : ℕ) < l then f (Fin.rev j) else 0 := by
  classical
  obtain ⟨l, hl, w, hwN, hww⟩ := exists_ggU_dual_family hσ hN hadj
  have hNN : ∀ x, N *ᵥ (N *ᵥ x) = 0 := fun x => by
    rw [Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
  let y : Fin l → (Fin n → F) := fun i => N *ᵥ w i
  have hyy : ∀ i j, ggUForm σ (y i) (y j) = 0 := fun i j => by
    simp only [y]
    rw [hadj, hNN, ggUForm_zero_right]
  obtain ⟨hl2, v, hvv, hwv, hyv⟩ := exists_ggU_middle_family hσ hwN hww hyy
  have hli : LinearIndependent F y := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h := congrArg (ggUForm σ (w i)) hc
    rw [ggUForm_sum_smul_right, ggUForm_zero_right] at h
    simpa only [y, hwN, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true] using h
  have hspan : Submodule.span F (Set.range y) = LinearMap.range N.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ⟨w i, rfl⟩)
    · rw [finrank_span_eq_card hli, Fintype.card_fin, hl]
  have hNv : ∀ j, N *ᵥ v j = 0 := by
    intro j
    refine eq_zero_of_ggUForm_right hσ.invol fun x => ?_
    rw [← hadj]
    have key : ∀ z ∈ Submodule.span F (Set.range y), ggUForm σ z (v j) = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact hyv i j
      | zero => exact ggUForm_zero_left σ _
      | add a b _ _ ha hb => rw [ggUForm_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [ggUForm_smul_left, ha, mul_zero]
    exact key _ (by rw [hspan]; exact ⟨x, rfl⟩)
  have hyw : ∀ i j, ggUForm σ (y i) (w j) = if i = j then 1 else 0 := fun i j => by
    rw [ggUForm_conj hσ.invol (w j) (y i), hwN]
    by_cases hij : i = j
    · rw [ite_eq_left hij.symm, ite_eq_left hij, map_one]
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij, map_zero]
  have hvw : ∀ i j, ggUForm σ (v i) (w j) = 0 := fun i j => by
    rw [ggUForm_conj hσ.invol (w j), hwv, map_zero]
  have hvy : ∀ i j, ggUForm σ (v i) (y j) = 0 := fun i j => by
    rw [ggUForm_conj hσ.invol (y j), hyv, map_zero]
  have hn : n = l + (n - 2 * l) + l := by omega
  let f : Fin n → (Fin n → F) := fun j =>
    Sum.elim w (Sum.elim v (fun b => y (Fin.rev b))) (ggBlockIdx l (n - 2 * l) hn j)
  have hf1 : ∀ (j : Fin n) (h : (j : ℕ) < l), f j = w ⟨j, h⟩ := fun j h => by
    simp only [f, ggBlockIdx_of_lt hn h, Sum.elim_inl]
  have hf2 : ∀ (j : Fin n) (h1 : l ≤ (j : ℕ)) (h2 : (j : ℕ) < l + (n - 2 * l)),
      f j = v ⟨j - l, by omega⟩ := fun j h1 h2 => by
    simp only [f, ggBlockIdx_of_mid hn h1 h2, Sum.elim_inl, Sum.elim_inr]
  have hf3 : ∀ (j : Fin n) (h : l + (n - 2 * l) ≤ (j : ℕ)),
      f j = y ⟨n - 1 - j, by have := j.isLt; omega⟩ := fun j h => by
    simp only [f, ggBlockIdx_of_ge hn h, Sum.elim_inr]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    have := j.isLt
    omega
  refine ⟨l, hl2, hl, f, fun i j => ?_, fun j => ?_⟩
  · have hi := i.isLt
    have hj := j.isLt
    have hrev : j = Fin.rev i ↔ (i : ℕ) + j + 1 = n := by
      rw [Fin.ext_iff, Fin.val_rev]
      omega
    have hz : ∀ {c : F}, c = 0 → ¬ ((i : ℕ) + j + 1 = n) →
        c = if j = Fin.rev i then 1 else 0 := fun hc h => by
      rw [hc, ite_eq_right (fun h' => h (hrev.mp h'))]
    rcases lt_or_ge (i : ℕ) l with hi1 | hi1
    · rw [hf1 i hi1]
      rcases lt_or_ge (j : ℕ) l with hj1 | hj1
      · exact hz (by rw [hf1 j hj1, hww]) (by omega)
      · rcases lt_or_ge (j : ℕ) (l + (n - 2 * l)) with hj2 | hj2
        · exact hz (by rw [hf2 j hj1 hj2, hwv]) (by omega)
        · rw [hf3 j hj2, hwN]
          by_cases h : (i : ℕ) + j + 1 = n
          · rw [ite_eq_left (Fin.ext (by simp only; omega)), ite_eq_left (hrev.mpr h)]
          · rw [ite_eq_right (fun h' => h (by have := congrArg Fin.val h'; simp only at this; omega)),
              ite_eq_right (fun h' => h (hrev.mp h'))]
    · rcases lt_or_ge (i : ℕ) (l + (n - 2 * l)) with hi2 | hi2
      · rw [hf2 i hi1 hi2]
        rcases lt_or_ge (j : ℕ) l with hj1 | hj1
        · exact hz (by rw [hf1 j hj1, hvw]) (by omega)
        · rcases lt_or_ge (j : ℕ) (l + (n - 2 * l)) with hj2 | hj2
          · rw [hf2 j hj1 hj2, hvv]
            by_cases h : (i : ℕ) + j + 1 = n
            · rw [ite_eq_left (Fin.ext (by simp only [Fin.val_rev]; omega)),
                ite_eq_left (hrev.mpr h)]
            · rw [ite_eq_right (fun h' => h (by
                  have := congrArg Fin.val h'
                  simp only [Fin.val_rev] at this
                  omega)), ite_eq_right (fun h' => h (hrev.mp h'))]
          · exact hz (by rw [hf3 j hj2, hvy]) (by omega)
      · rw [hf3 i hi2]
        rcases lt_or_ge (j : ℕ) l with hj1 | hj1
        · rw [hf1 j hj1, hyw]
          by_cases h : (i : ℕ) + j + 1 = n
          · rw [ite_eq_left (Fin.ext (by simp only; omega)), ite_eq_left (hrev.mpr h)]
          · rw [ite_eq_right (fun h' => h (by have := congrArg Fin.val h'; simp only at this; omega)),
              ite_eq_right (fun h' => h (hrev.mp h'))]
        · rcases lt_or_ge (j : ℕ) (l + (n - 2 * l)) with hj2 | hj2
          · exact hz (by rw [hf2 j hj1 hj2, hyv]) (by omega)
          · exact hz (by rw [hf3 j hj2, hyy]) (by omega)
  · have hj := j.isLt
    rcases lt_or_ge (j : ℕ) l with hj1 | hj1
    · rw [ite_eq_left hj1, hf1 j hj1, hf3 (Fin.rev j) (by simp only [Fin.val_rev]; omega)]
      simp only [y]
      congr 2
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    · rw [ite_eq_right (by omega)]
      rcases lt_or_ge (j : ℕ) (l + (n - 2 * l)) with hj2 | hj2
      · rw [hf2 j hj1 hj2, hNv]
      · rw [hf3 j hj2]
        exact hNN _

end Adapted

section Involutions

variable {F : Type*} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {n : ℕ}

theorem exists_conj_ggInvSU_of_orderOf_eq_two (hσ : IsUnitaryInvolution σ) {u : SU σ n}
    (hu : orderOf u = 2) :
    ∃ l : ℕ, 1 ≤ l ∧ 2 * l ≤ n ∧ ∃ a : SU σ n, u = a * ggInvSU σ n l * a⁻¹ := by
  classical
  set U : Matrix (Fin n) (Fin n) F := mat σ n u with hUdef
  have hU2 : U * U = 1 := by
    have h := congrArg (mat σ n) (pow_orderOf_eq_one u)
    rwa [hu, pow_two, map_mul, map_one] at h
  have hUiso : conjTr σ U * antidiag n * U = antidiag n := conjTr_mat_mul u
  obtain ⟨l, hl, hlr, f, hgram, hact⟩ := exists_ggU_adapted_family hσ
    (sub_one_mul_sub_one_eq_zero_charTwo hU2) (ggUForm_sub_one_mulVec hUiso hU2)
  have hl1 : 1 ≤ l := by
    by_contra h0
    have hbot : LinearMap.range (U - 1).mulVecLin = ⊥ :=
      Submodule.finrank_eq_zero.mp (by omega)
    have hN0 : U - 1 = 0 := by
      ext i j
      have hx : (U - 1) *ᵥ Pi.single j 1 ∈ LinearMap.range (U - 1).mulVecLin := ⟨_, rfl⟩
      rw [hbot, Submodule.mem_bot] at hx
      have := congrFun hx i
      simpa [Matrix.mulVec_single_one] using this
    have hu1 : u = 1 := mat_injective (by rw [map_one]; exact sub_eq_zero.mp hN0)
    rw [hu1, orderOf_one] at hu
    exact absurd hu (by norm_num)
  set A : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => f j i with hA
  have hAiso : conjTr σ A * antidiag n * A = antidiag n := by
    ext i j
    rw [conjTr_mul_antidiag_mul_apply_eq_ggUForm]
    exact (hgram i j).trans (by simp [antidiag])
  have hUA : U * A = A * ggInvUMatrix n l F := by
    ext i j
    have hL : (U * A) i j = (U *ᵥ f j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, A]
    have hUf : U *ᵥ f j = f j + (U - 1) *ᵥ f j := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [hL, hUf, hact j, ggInvUMatrix, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply,
      Pi.add_apply, Matrix.mul_apply]
    congr 1
    split_ifs with hj
    · have hjn := j.isLt
      rw [Finset.sum_eq_single (Fin.rev j)]
      · rw [ggInvUNil_apply, ite_eq_left ⟨hj, by simp only [Fin.val_rev]; omega,
          by simp only [Fin.val_rev]; omega⟩, mul_one]
        rfl
      · intro t _ ht
        rw [ggInvUNil_apply, ite_eq_right (fun h => ht (Fin.ext (by
          simp only [Fin.val_rev]
          omega))), mul_zero]
      · simp
    · simp only [Pi.zero_apply]
      symm
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [ggInvUNil_apply, ite_eq_right (fun h => hj h.1), mul_zero]
  have hdetJ := det_antidiag_ne_zero (F := F) n
  set d := A.det with hd
  have hσd : σ d * d = 1 := by
    have h := congrArg Matrix.det hAiso
    have hmap : (A.map σ).det = σ A.det := (RingHom.map_det (σ : F →+* F) A).symm
    rw [Matrix.det_mul, Matrix.det_mul, conjTr, Matrix.det_transpose, hmap] at h
    have h' : (σ d * d - 1) * (antidiag n : Matrix (Fin n) (Fin n) F).det = 0 := by
      change σ d * (antidiag n : Matrix (Fin n) (Fin n) F).det * d =
        (antidiag n : Matrix (Fin n) (Fin n) F).det at h
      linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · linear_combination h''
    · exact absurd h'' hdetJ
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hσd
    exact zero_ne_one hσd
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' d⁻¹
  have hσμ : σ μ * μ = 1 := by
    refine eq_of_mul_self_eq_mul_self_charTwo ?_
    calc σ μ * μ * (σ μ * μ) = σ (μ * μ) * (μ * μ) := by rw [map_mul]; ring
      _ = σ d⁻¹ * d⁻¹ := by rw [← hμ]
      _ = (σ d * d)⁻¹ := by rw [map_inv₀, mul_inv]
      _ = 1 * 1 := by rw [hσd, inv_one, one_mul]
  have hn2 : 2 ≤ n := by omega
  set e : Fin n → F := Pi.mulSingle (⟨0, by omega⟩ : Fin n) μ *
    Pi.mulSingle (Fin.rev (⟨0, by omega⟩ : Fin n)) μ with he
  have he_val : ∀ x : Fin n, e x = if (x : ℕ) = 0 ∨ (x : ℕ) = n - 1 then μ else 1 := by
    intro x
    have := x.isLt
    simp only [he, Pi.mul_apply, Pi.mulSingle_apply, Fin.ext_iff, Fin.val_rev]
    split_ifs <;> first | (exfalso; omega) | simp
  have hprod : ∏ x, e x = μ * μ := by
    simp only [he, Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
      Finset.mem_univ, ite_true]
  have hDiso : conjTr σ (Matrix.diagonal e) * antidiag n * Matrix.diagonal e = antidiag n := by
    ext a b
    have ha := a.isLt
    rw [conjTr, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    simp only [antidiag, of_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    split_ifs with hab
    · subst hab
      rw [he_val, he_val]
      simp only [Fin.val_rev]
      split_ifs <;> first | (exfalso; omega) | simp [hσμ]
    · rfl
  have hDcomm : ggInvUMatrix n l F * Matrix.diagonal e = Matrix.diagonal e * ggInvUMatrix n l F := by
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [ggInvUMatrix, Matrix.add_apply, Matrix.one_apply, ggInvUNil_apply]
    by_cases hab : a = b
    · subst hab
      ring
    · rw [ite_eq_right hab, zero_add]
      split_ifs with h
      · rw [one_mul, mul_one, he_val, he_val]
        have := a.isLt
        split_ifs <;> first | rfl | (exfalso; omega)
      · rw [mul_zero, zero_mul]
  have hADdet : (A * Matrix.diagonal e).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_diagonal, hprod, ← hμ, ← hd, mul_inv_cancel₀ hd0]
  have hADiso : conjTr σ (A * Matrix.diagonal e) * antidiag n * (A * Matrix.diagonal e) =
      antidiag n := by
    rw [conjTr_mul]
    calc conjTr σ (Matrix.diagonal e) * conjTr σ A * antidiag n * (A * Matrix.diagonal e) =
        conjTr σ (Matrix.diagonal e) * (conjTr σ A * antidiag n * A) * Matrix.diagonal e := by
          simp only [Matrix.mul_assoc]
      _ = antidiag n := by rw [hAiso, hDiso]
  let g : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (A * Matrix.diagonal e)
    (by rw [hADdet]; exact one_ne_zero)
  have hg : g ∈ SU σ n := ⟨hADdet, hADiso⟩
  let a : SU σ n := ⟨g, hg⟩
  refine ⟨l, hl1, hl, a, ?_⟩
  have hua : u * a = a * ggInvSU σ n l := by
    apply mat_injective
    rw [map_mul, map_mul]
    change U * (A * Matrix.diagonal e) = A * Matrix.diagonal e * mat σ n (ggInvSU σ n l)
    rw [mat_apply, coe_ggInvSU σ hl, ← Matrix.mul_assoc, hUA, Matrix.mul_assoc,
      Matrix.mul_assoc, hDcomm]
  calc u = u * a * a⁻¹ := by group
    _ = a * ggInvSU σ n l * a⁻¹ := by rw [hua]

end Involutions

theorem ggSUInvolutionClassInput : GGSUInvolutionClassInput := by
  intro f n hf u hu
  exact exists_conj_ggInvSU_of_orderOf_eq_two
    (isUnitaryInvolution_unitaryInvolution (card_galoisField_two_mul 2 f hf)) hu

end CFSG.StandardType
