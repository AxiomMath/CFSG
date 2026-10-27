module

public import CFSG.Quasithin.H13.NQCatL34AutPoint

public section

namespace CFSG.Quasithin.H13.NQCat.L34Aut

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter Matrix

section Flag

variable {n : ℕ} {K : Type*} [Field K] [Finite K]

theorem map_flagSpace_eq_iff (A : GL (Fin n) K) {i : ℕ} :
    (flagSpace n K i).map (mulVecLin (A : Matrix (Fin n) (Fin n) K)) = flagSpace n K i ↔
      ∀ r c : Fin n, (c : ℕ) < i → i ≤ (r : ℕ) → (A : Matrix (Fin n) (Fin n) K) r c = 0 := by
  constructor
  · intro h r c hc hr
    have h1 : (A : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single c 1 ∈ flagSpace n K i := by
      rw [← h]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨c, hc, rfl⟩)
    have h2 := (mem_flagSpace.1 h1) r hr
    rwa [mulVec_single_one, col_apply] at h2
  · intro h
    refine Submodule.eq_of_le_of_finrank_eq ?_ (finrank_map_mulVecLin_gl A _)
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, mulVecLin_apply, mem_flagSpace]
    intro r hr
    rw [mulVec_single_one, col_apply]
    exact h r c hc hr

theorem mem_stabilizer_flagSpace_iff (g : SpecialLinearGroup (Fin n) K) {i : ℕ} :
    g ∈ stabilizer (flagSpace n K i) ↔
      ∀ r c : Fin n, (c : ℕ) < i → i ≤ (r : ℕ) → (g : Matrix (Fin n) (Fin n) K) r c = 0 :=
  map_flagSpace_eq_iff (SpecialLinearGroup.toGL g)

end Flag

section Model

variable {k : Type} [Field k]

theorem mem_dotOrth_flag_one {v : Fin 3 → k} : v ∈ dotOrth (flagSpace 3 k 1) ↔ v 0 = 0 := by
  rw [mem_dotOrth]
  constructor
  · intro h
    have h1 := h (Pi.single 0 1) (Submodule.subset_span ⟨0, by decide, rfl⟩)
    simpa using h1
  · intro h w hw
    have hw1 := (mem_flagSpace.1 hw) 1 (by decide)
    have hw2 := (mem_flagSpace.1 hw) 2 (by decide)
    simp [dotProduct, Fin.sum_univ_three, h, hw1, hw2]

theorem mem_dotOrth_flag_two {v : Fin 3 → k} :
    v ∈ dotOrth (flagSpace 3 k 2) ↔ v 0 = 0 ∧ v 1 = 0 := by
  rw [mem_dotOrth]
  constructor
  · intro h
    have h0 := h (Pi.single 0 1) (Submodule.subset_span ⟨0, by decide, rfl⟩)
    have h1 := h (Pi.single 1 1) (Submodule.subset_span ⟨1, by decide, rfl⟩)
    exact ⟨by simpa using h0, by simpa using h1⟩
  · rintro ⟨h0, h1⟩ w hw
    have hw2 := (mem_flagSpace.1 hw) 2 (by decide)
    simp [dotProduct, Fin.sum_univ_three, h0, h1, hw2]

theorem coordImage_dotOrth_flag_one (σ : k ≃+* k) :
    coordImage σ (dotOrth (flagSpace 3 k 1)) = dotOrth (flagSpace 3 k 1) := by
  ext v
  rw [mem_coordImage, mem_dotOrth_flag_one, mem_dotOrth_flag_one,
    map_eq_zero_iff _ σ.symm.injective]

theorem coordImage_dotOrth_flag_two (σ : k ≃+* k) :
    coordImage σ (dotOrth (flagSpace 3 k 2)) = dotOrth (flagSpace 3 k 2) := by
  ext v
  rw [mem_coordImage, mem_dotOrth_flag_two, mem_dotOrth_flag_two,
    map_eq_zero_iff _ σ.symm.injective, map_eq_zero_iff _ σ.symm.injective]

theorem finrank_flag_one : finrank k (flagSpace 3 k 1) = 1 := finrank_flagSpace (by norm_num)

theorem finrank_flag_two : finrank k (flagSpace 3 k 2) = 2 := finrank_flagSpace (by norm_num)

variable [Finite k]

theorem swap_nf (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    {β : MulAut (projectiveSL 3 k)}
    (h1 : (projStabilizer (flagSpace 3 k 1)).map β.toMonoidHom = projStabilizer (flagSpace 3 k 2))
    (h2 : (projStabilizer (flagSpace 3 k 2)).map β.toMonoidHom =
      projStabilizer (flagSpace 3 k 1)) :
    ∃ (A : GL (Fin 3) k) (a : ZMod 2), β = nf σ A a 1 ∧
      (A : Matrix (Fin 3) (Fin 3) k) 1 2 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) k) 2 2 = 0 ∧
        (A : Matrix (Fin 3) (Fin 3) k) 2 1 = 0 := by
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  obtain ⟨⟨A, a, b⟩, rfl⟩ := exists_nf hσ hk β
  have hdA : ∀ W : Submodule k (Fin 3 → k),
      finrank k (W.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) k))) = finrank k W :=
    finrank_map_mulVecLin_gl A
  rcases zmod_two_cases b with rfl | rfl
  · exfalso
    rcases zmod_two_cases a with rfl | rfl
    · simp only [nf, ZMod.val_zero, pow_zero, mul_one] at h1
      rw [map_projStabilizer_conjAut] at h1
      have h3 := eq_of_projStabilizer_eq (by rw [hdA, finrank_flag_one]; omega)
        (by rw [finrank_flag_two]; omega) h1
      have h4 := congrArg (fun W : Submodule k (Fin 3 → k) => finrank k W) h3
      simp only [hdA, finrank_flag_one, finrank_flag_two] at h4
      omega
    · simp only [nf, ZMod.val_zero, val_one_two, pow_zero, pow_one, mul_one] at h1
      rw [map_mul_toMonoidHom', map_projStabilizer_fieldAut, map_projStabilizer_conjAut] at h1
      have h3 := eq_of_projStabilizer_eq
        (by rw [hdA, finrank_coordImage, finrank_flag_one]; omega)
        (by rw [finrank_flag_two]; omega) h1
      have h4 := congrArg (fun W : Submodule k (Fin 3 → k) => finrank k W) h3
      simp only [hdA, finrank_coordImage, finrank_flag_one, finrank_flag_two] at h4
      omega
  ·
    have hA : (dotOrth (flagSpace 3 k 1)).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) k)) =
          flagSpace 3 k 2 ∧
        (dotOrth (flagSpace 3 k 2)).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) k)) =
          flagSpace 3 k 1 := by
      have hd1 : finrank k (dotOrth (flagSpace 3 k 1)) = 2 := by
        rw [finrank_dotOrth, finrank_flag_one]
      have hd2 : finrank k (dotOrth (flagSpace 3 k 2)) = 1 := by
        rw [finrank_dotOrth, finrank_flag_two]
      rcases zmod_two_cases a with rfl | rfl
      · simp only [nf, ZMod.val_zero, val_one_two, pow_zero, pow_one, mul_one] at h1 h2
        rw [map_mul_toMonoidHom', map_projStabilizer_dualAut, map_projStabilizer_conjAut] at h1 h2
        exact ⟨eq_of_projStabilizer_eq (by rw [hdA, hd1]; omega)
            (by rw [finrank_flag_two]; omega) h1,
          eq_of_projStabilizer_eq (by rw [hdA, hd2]; omega) (by rw [finrank_flag_one]; omega) h2⟩
      · simp only [nf, val_one_two, pow_one] at h1 h2
        rw [map_mul_toMonoidHom', map_mul_toMonoidHom', map_projStabilizer_dualAut,
          map_projStabilizer_fieldAut, map_projStabilizer_conjAut,
          coordImage_dotOrth_flag_one] at h1
        rw [map_mul_toMonoidHom', map_mul_toMonoidHom', map_projStabilizer_dualAut,
          map_projStabilizer_fieldAut, map_projStabilizer_conjAut,
          coordImage_dotOrth_flag_two] at h2
        exact ⟨eq_of_projStabilizer_eq (by rw [hdA, hd1]; omega)
            (by rw [finrank_flag_two]; omega) h1,
          eq_of_projStabilizer_eq (by rw [hdA, hd2]; omega) (by rw [finrank_flag_one]; omega) h2⟩
    have he2 : (A : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 2 1 ∈ flagSpace 3 k 1 := by
      rw [← hA.2]
      exact Submodule.mem_map_of_mem (mem_dotOrth_flag_two.2 ⟨by simp, by simp⟩)
    have he1 : (A : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 1 1 ∈ flagSpace 3 k 2 := by
      rw [← hA.1]
      exact Submodule.mem_map_of_mem (mem_dotOrth_flag_one.2 (by simp))
    have h12 := (mem_flagSpace.1 he2) 1 (by decide)
    have h22 := (mem_flagSpace.1 he2) 2 (by decide)
    have h21 := (mem_flagSpace.1 he1) 2 (by decide)
    rw [mulVec_single_one, col_apply] at h12 h22 h21
    exact ⟨A, a, rfl, h12, h22, h21⟩

end Model

section Matrices

variable {k : Type} [Field k]

@[expose] def w0GL : GL (Fin 3) k :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_w0GL : ((w0GL : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
    !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl

theorem w0GL_inv : (w0GL : GL (Fin 3) k)⁻¹ = w0GL := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  change !![(0 : k), 0, 1; 0, 1, 0; 1, 0, 0] * !![(0 : k), 0, 1; 0, 1, 0; 1, 0, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def midDiagGL (y : kˣ) : GL (Fin 3) k :=
  ⟨!![1, 0, 0; 0, (y : k), 0; 0, 0, 1], !![1, 0, 0; 0, ((y⁻¹ : kˣ) : k), 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

end Matrices

section Twist

variable {k : Type} [Field k]

theorem twistF_zero (σ : k ≃+* k) (B : GL (Fin 3) k) : twistF σ 0 B = B := by
  simp [twistF]

theorem twistD_zero (B : GL (Fin 3) k) : twistD 0 B = B := by
  simp [twistD]

theorem twistD_one' (B : GL (Fin 3) k) : twistD 1 B = GeneralLinearGroup.inverseTranspose B := by
  simp [twistD]

theorem twistF_one' (σ : k ≃+* k) (B : GL (Fin 3) k) :
    twistF σ 1 B = GeneralLinearGroup.map (σ : k →+* k) B := by
  simp [twistF]

theorem inverseTranspose_w0GL :
    GeneralLinearGroup.inverseTranspose (w0GL : GL (Fin 3) k) = w0GL := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose, w0GL_inv, coe_w0GL]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem map_w0GL (σ : k ≃+* k) : GeneralLinearGroup.map (σ : k →+* k) (w0GL : GL (Fin 3) k) =
    w0GL := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.map_apply, coe_w0GL]
  fin_cases i <;> fin_cases j <;> simp

end Twist

section Square

variable {k : Type} [Field k] [Finite k]

theorem flag_of_swap_shape {A : GL (Fin 3) k} (hA12 : (A : Matrix (Fin 3) (Fin 3) k) 1 2 = 0)
    (hA22 : (A : Matrix (Fin 3) (Fin 3) k) 2 2 = 0) (hA21 : (A : Matrix (Fin 3) (Fin 3) k) 2 1 = 0)
    {i : ℕ} (hi : i = 1 ∨ i = 2) :
    (flagSpace 3 k i).map (mulVecLin ((A * w0GL : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) =
        flagSpace 3 k i ∧
      (flagSpace 3 k i).map (mulVecLin (((A * w0GL)⁻¹ : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k)) = flagSpace 3 k i := by
  have hC : (flagSpace 3 k i).map (mulVecLin ((A * w0GL : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k)) = flagSpace 3 k i := by
    refine (map_flagSpace_eq_iff _).2 fun r c hc hr => ?_
    rcases hi with rfl | rfl <;> fin_cases r <;> fin_cases c <;>
      simp_all [coe_w0GL, Matrix.mul_apply, Fin.sum_univ_three]
  refine ⟨hC, ?_⟩
  conv_lhs => rw [← hC]
  rw [← Submodule.map_comp, ← mulVecLin_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    mulVecLin_one, Submodule.map_id]

theorem swap_aut_square (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    {β : MulAut (projectiveSL 3 k)}
    (h1 : (projStabilizer (flagSpace 3 k 1)).map β.toMonoidHom = projStabilizer (flagSpace 3 k 2))
    (h2 : (projStabilizer (flagSpace 3 k 2)).map β.toMonoidHom =
      projStabilizer (flagSpace 3 k 1))
    (hinn : β * β ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range) :
    ∃ M : SpecialLinearGroup (Fin 3) k, M ∈ stabilizer (flagSpace 3 k 1) ∧
      M ∈ stabilizer (flagSpace 3 k 2) ∧
        MulAut.conj (proj 3 k M) * β * (MulAut.conj (proj 3 k M) * β) = 1 := by
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  have hff := fieldAut_sigma_mul_self hσ hk
  obtain ⟨A, a, rfl, hA12, hA22, hA21⟩ := swap_nf hk hσ h1 h2
  set C : GL (Fin 3) k := A * w0GL with hCdef
  have hflag := fun {i : ℕ} (hi : i = 1 ∨ i = 2) => flag_of_swap_shape hA12 hA22 hA21 hi
  have hsq : ∀ M : SpecialLinearGroup (Fin 3) k,
      MulAut.conj (proj 3 k M) * nf σ A a 1 * (MulAut.conj (proj 3 k M) * nf σ A a 1) =
        conjAut 3 k (SpecialLinearGroup.toGL M * A *
          twistF σ a (twistD 1 (SpecialLinearGroup.toGL M * A))) := by
    intro M
    rw [← conjAut_toGL, ← nf_zero_zero σ, nf_mul σ hff, twistD_zero, twistF_zero, zero_add,
      zero_add, nf_mul σ hff, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, nf_zero_zero]
  rcases zmod_two_cases a with rfl | rfl
  ·
    set D : GL (Fin 3) k := midDiagGL (GeneralLinearGroup.det C) with hDdef
    have hdetD : GeneralLinearGroup.det D = GeneralLinearGroup.det C := by
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, hDdef]
      change Matrix.det !![1, 0, 0; 0, ((GeneralLinearGroup.det C : kˣ) : k), 0; 0, 0, 1] = _
      rw [Matrix.det_fin_three]
      simp
    have hdetM : Matrix.det ((D * C⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1 := by
      rw [← GeneralLinearGroup.val_det_apply, map_mul, map_inv, hdetD, mul_inv_cancel,
        Units.val_one]
    set M : SpecialLinearGroup (Fin 3) k := ⟨_, hdetM⟩ with hMdef
    have hMGL : SpecialLinearGroup.toGL M = D * C⁻¹ := Units.ext rfl
    have hDF : ∀ {i : ℕ}, i = 1 ∨ i = 2 →
        (flagSpace 3 k i).map (mulVecLin (D : Matrix (Fin 3) (Fin 3) k)) = flagSpace 3 k i := by
      intro i hi
      refine (map_flagSpace_eq_iff _).2 fun r c hc hr => ?_
      rcases hi with rfl | rfl <;> fin_cases r <;> fin_cases c <;> simp_all [midDiagGL]
    have hMF : ∀ {i : ℕ}, i = 1 ∨ i = 2 → M ∈ stabilizer (flagSpace 3 k i) := by
      intro i hi
      rw [mem_stabilizer]
      change (flagSpace 3 k i).map (mulVecLin ((D * C⁻¹ : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k)) = _
      rw [Units.val_mul, mulVecLin_mul, Submodule.map_comp, (hflag hi).2, hDF hi]
    refine ⟨M, hMF (Or.inl rfl), hMF (Or.inr rfl), ?_⟩
    rw [hsq, hMGL, twistF_zero, twistD_one']
    have hX : D * C⁻¹ * A = D * w0GL := by
      rw [hCdef, _root_.mul_inv_rev, w0GL_inv]
      group
    rw [hX]
    convert map_one (conjAut 3 k)
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_inverseTranspose, _root_.mul_inv_rev, w0GL_inv,
      Units.val_one]
    change (D : Matrix (Fin 3) (Fin 3) k) * !![0, 0, 1; 0, 1, 0; 1, 0, 0] *
      ((!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) k) *
        ((D⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k))ᵀ = 1
    have hDinv : ((D⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        !![1, 0, 0; 0, (((GeneralLinearGroup.det C)⁻¹ : kˣ) : k), 0; 0, 0, 1] := rfl
    rw [hDinv]
    change !![1, 0, 0; 0, ((GeneralLinearGroup.det C : kˣ) : k), 0; 0, 0, 1] *
      !![(0 : k), 0, 1; 0, 1, 0; 1, 0, 0] * _ = _
    have hCdet : (C : Matrix (Fin 3) (Fin 3) k).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact (GeneralLinearGroup.det C).ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hCdet]
  ·
    have hdetA : GeneralLinearGroup.det A = 1 := by
      have h3 : nf σ A 1 1 * nf σ A 1 1 = conjAut 3 k (A * twistF σ 1 (twistD 1 A)) := by
        rw [nf_mul σ hff, CharTwo.add_self_eq_zero, nf_zero_zero]
      rw [h3, conjAut_mem_range_conj_iff hk, map_mul, det_twist hσ hk] at hinn
      simp only [CharTwo.add_self_eq_zero, ↓reduceIte] at hinn
      have h4 := units_pow_three hk (GeneralLinearGroup.det A)
      calc GeneralLinearGroup.det A = GeneralLinearGroup.det A ^ 3 *
            (GeneralLinearGroup.det A * GeneralLinearGroup.det A)⁻¹ := by group
        _ = 1 := by rw [h4, hinn, inv_one, one_mul]
    have hdetw : GeneralLinearGroup.det (w0GL : GL (Fin 3) k) = 1 := by
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, coe_w0GL, Matrix.det_fin_three]
      simp [CharTwo.neg_eq]
    have hdetM : Matrix.det ((C⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1 := by
      rw [← GeneralLinearGroup.val_det_apply, map_inv, hCdef, map_mul, hdetA, hdetw, one_mul,
        inv_one, Units.val_one]
    set M : SpecialLinearGroup (Fin 3) k := ⟨_, hdetM⟩ with hMdef
    have hMGL : SpecialLinearGroup.toGL M = C⁻¹ := Units.ext rfl
    have hMF : ∀ {i : ℕ}, i = 1 ∨ i = 2 → M ∈ stabilizer (flagSpace 3 k i) := by
      intro i hi
      rw [mem_stabilizer]
      exact (hflag hi).2
    refine ⟨M, hMF (Or.inl rfl), hMF (Or.inr rfl), ?_⟩
    rw [hsq, hMGL, twistF_one', twistD_one']
    have hX : C⁻¹ * A = w0GL := by
      rw [hCdef, _root_.mul_inv_rev, w0GL_inv]
      group
    rw [hX, inverseTranspose_w0GL, map_w0GL]
    convert map_one (conjAut 3 k)
    calc (w0GL : GL (Fin 3) k) * w0GL = w0GL * w0GL⁻¹ := by rw [w0GL_inv]
      _ = 1 := mul_inv_cancel _

end Square

section GraphMatrices

variable {k : Type} [Field k] [CharP k 2]

theorem graph_key_identity {ω p p' z x a d : k} (hω : ω ^ 2 + ω + 1 = 0)
    (hp : p ^ 2 * d = ω * z) (hp' : a * p' = ω * x + ω ^ 2 * d * p) :
    !![ω, p, 0; 0, 1, p'; 0, 0, ω ^ 2] * !![z, x, a; x, d, 0; a, 0, 0] *
      (!![ω, p, 0; 0, 1, p'; 0, 0, ω ^ 2])ᵀ = !![z, x, a; x, d, 0; a, 0, 0] := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
    | ring1
    | linear_combination z * hω + hp + (ω * p * x - z) * h2
    | linear_combination ω * hp' + (x + p * d * (ω - 1)) * hω + (p * d - x) * h2
    | linear_combination a * (ω - 1) * hω

omit [CharP k 2] in
theorem graph_cube {ω p p' : k} (hω : ω ^ 2 + ω + 1 = 0) :
    (!![ω, p, 0; 0, 1, p'; 0, 0, ω ^ 2] : Matrix (Fin 3) (Fin 3) k) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
    | ring1
    | linear_combination (ω - 1) * hω
    | linear_combination p * hω
    | linear_combination p * p' * hω
    | linear_combination (p' + p' * ω * (ω - 1)) * hω
    | linear_combination (ω - 1) * (ω ^ 3 + 1) * hω

end GraphMatrices

section Graph

variable {k : Type} [Field k]

theorem graph_shape (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    {A : GL (Fin 3) k} (hA12 : (A : Matrix (Fin 3) (Fin 3) k) 1 2 = 0)
    (hA22 : (A : Matrix (Fin 3) (Fin 3) k) 2 2 = 0) (hA21 : (A : Matrix (Fin 3) (Fin 3) k) 2 1 = 0)
    (hβ : nf σ A 0 1 * nf σ A 0 1 = 1) :
    (A : Matrix (Fin 3) (Fin 3) k) 1 0 = (A : Matrix (Fin 3) (Fin 3) k) 0 1 ∧
      (A : Matrix (Fin 3) (Fin 3) k) 2 0 = (A : Matrix (Fin 3) (Fin 3) k) 0 2 ∧
      (A : Matrix (Fin 3) (Fin 3) k) 0 2 ≠ 0 ∧ (A : Matrix (Fin 3) (Fin 3) k) 1 1 ≠ 0 := by
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  have hff := fieldAut_sigma_mul_self hσ hk
  have hdet : (A : Matrix (Fin 3) (Fin 3) k).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact (GeneralLinearGroup.det A).ne_zero
  rw [Matrix.det_fin_three, hA12, hA22, hA21] at hdet
  have h02 : (A : Matrix (Fin 3) (Fin 3) k) 0 2 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have h11 : (A : Matrix (Fin 3) (Fin 3) k) 1 1 ≠ 0 := fun h => hdet (by rw [h]; ring)
  rw [nf_mul σ hff, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, nf_zero_zero,
    twistF_zero, twistD_one'] at hβ
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) (K := k) le_rfl
    (A * GeneralLinearGroup.inverseTranspose A) (RingEquiv.refl k)
    (by rw [show (RingEquiv.refl k) = 1 from rfl, map_one (fieldAut 3 k), mul_one]; exact hβ)
  have h1 : (Matrix.scalar (Fin 3) (c : k)) * (A : Matrix (Fin 3) (Fin 3) k)ᵀ =
      (A : Matrix (Fin 3) (Fin 3) k) := by
    have h2 := congrArg (fun g : GL (Fin 3) k =>
      (g : Matrix (Fin 3) (Fin 3) k) * (A : Matrix (Fin 3) (Fin 3) k)ᵀ) hc
    simp only [GeneralLinearGroup.coe_scalar, Units.val_mul,
      GeneralLinearGroup.coe_inverseTranspose] at h2
    rw [h2, Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.mul_one]
  have he : ∀ i j, (c : k) * (A : Matrix (Fin 3) (Fin 3) k) j i =
      (A : Matrix (Fin 3) (Fin 3) k) i j := fun i j => by
    have := congrFun (congrFun h1 i) j
    rwa [Matrix.scalar_apply, diagonal_mul, transpose_apply] at this
  have hc1 : (c : k) = 1 := by
    have h3 := he 1 1
    exact (mul_eq_right₀ h11).1 h3
  refine ⟨?_, ?_, h02, h11⟩
  · have h3 := he 1 0
    rw [hc1, one_mul] at h3
    exact h3.symm
  · have h3 := he 2 0
    rw [hc1, one_mul] at h3
    exact h3.symm

theorem swap_graph_fixed [Finite k] (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    {A : GL (Fin 3) k} (hA12 : (A : Matrix (Fin 3) (Fin 3) k) 1 2 = 0)
    (hA22 : (A : Matrix (Fin 3) (Fin 3) k) 2 2 = 0) (hA21 : (A : Matrix (Fin 3) (Fin 3) k) 2 1 = 0)
    (hβ : nf σ A 0 1 * nf σ A 0 1 = 1) :
    ∃ Y : SpecialLinearGroup (Fin 3) k, Y ∈ stabilizer (flagSpace 3 k 1) ∧
      Y ∈ stabilizer (flagSpace 3 k 2) ∧ orderOf (proj 3 k Y) = 3 ∧
        nf σ A 0 1 (proj 3 k Y) = proj 3 k Y := by
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  obtain ⟨h10, h20, h02, h11⟩ := graph_shape hk hσ hA12 hA22 hA21 hβ
  set z := (A : Matrix (Fin 3) (Fin 3) k) 0 0 with hz
  set x := (A : Matrix (Fin 3) (Fin 3) k) 0 1 with hx
  set a := (A : Matrix (Fin 3) (Fin 3) k) 0 2 with ha
  set d := (A : Matrix (Fin 3) (Fin 3) k) 1 1 with hd
  have hAeq : (A : Matrix (Fin 3) (Fin 3) k) = !![z, x, a; x, d, 0; a, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hz, hx, ha, hd, h10, h20, hA12, hA22, hA21]
  obtain ⟨u, hu⟩ := CFSG.RankThree.PartTwo.KFacts.L34.exists_units_ne_one hk
  set ω : k := (u : k) with hωdef
  have hω3 : ω ^ 3 = 1 := by
    have h1 := congrArg Units.val (units_pow_three hk u)
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h1
  have hω1 : ω ≠ 1 := fun h => hu (Units.ext h)
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hω1)
  set p := (frobeniusEquiv k 2).symm (ω * z / d) with hpdef
  have hp : p ^ 2 * d = ω * z := by
    have h1 : p ^ 2 = ω * z / d := by
      have h2 := (frobeniusEquiv k 2).apply_symm_apply (ω * z / d)
      rwa [frobeniusEquiv_apply, frobenius_def] at h2
    rw [h1, div_mul_cancel₀ _ h11]
  set p' := (ω * x + ω ^ 2 * d * p) / a with hp'def
  have hp' : a * p' = ω * x + ω ^ 2 * d * p := by rw [hp'def, mul_div_cancel₀ _ h02]
  set YM : Matrix (Fin 3) (Fin 3) k := !![ω, p, 0; 0, 1, p'; 0, 0, ω ^ 2] with hYM
  have hdetY : YM.det = 1 := by
    rw [Matrix.det_fin_three]
    simp [hYM]
    linear_combination hω3
  obtain ⟨Y, hYc⟩ : ∃ Y : SpecialLinearGroup (Fin 3) k, (Y : Matrix (Fin 3) (Fin 3) k) = YM :=
    ⟨⟨YM, hdetY⟩, rfl⟩
  refine ⟨Y, (mem_stabilizer_flagSpace_iff Y).2 fun r c hc hr => ?_,
    (mem_stabilizer_flagSpace_iff Y).2 fun r c hc hr => ?_, ?_, ?_⟩
  · rw [hYc]
    fin_cases r <;> fin_cases c <;> first | rfl | (simp at hc hr)
  · rw [hYc]
    fin_cases r <;> fin_cases c <;> first | rfl | (simp at hc hr)
  ·
    have hY3 : Y ^ 3 = 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [Matrix.SpecialLinearGroup.coe_pow, hYc, hYM, graph_cube hω,
        Matrix.SpecialLinearGroup.coe_one]
    have hne : proj 3 k Y ≠ 1 := by
      intro h
      rw [proj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      obtain ⟨c, -, hc⟩ := h
      have h00 := congrFun (congrFun hc 0) 0
      have h11' := congrFun (congrFun hc 1) 1
      rw [hYc] at h00 h11'
      simp only [hYM, Matrix.scalar_apply, diagonal_apply_eq] at h00 h11'
      exact hω1 (h00.trans h11'.symm)
    exact orderOf_eq_prime (by rw [← map_pow, hY3, map_one]) hne
  ·
    simp only [nf, ZMod.val_zero, val_one_two, pow_zero, pow_one, mul_one, MulAut.mul_apply]
    rw [dualAut_proj, conjAut_proj]
    congr 1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose]
    have hYinv : ((Y⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * YM = 1 := by
      rw [Matrix.SpecialLinearGroup.coe_inv, ← hYc, adjugate_mul, Y.2, one_smul]
    have hkey := graph_key_identity hω hp hp'
    rw [← hYM, ← hAeq] at hkey
    have hcalc : (A : Matrix (Fin 3) (Fin 3) k) *
          ((Y⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)ᵀ *
          ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = YM :=
      calc (A : Matrix (Fin 3) (Fin 3) k) *
            ((Y⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)ᵀ *
            ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
          = YM * A * YMᵀ * ((Y⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)ᵀ *
            ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by rw [hkey]
        _ = YM * A * (((Y⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * YM)ᵀ *
            ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
        _ = YM := by
          rw [hYinv, transpose_one, Matrix.mul_one, Matrix.mul_assoc, Units.mul_inv,
            Matrix.mul_one]
    rw [hcalc, hYc]

end Graph

end CFSG.Quasithin.H13.NQCat.L34Aut
