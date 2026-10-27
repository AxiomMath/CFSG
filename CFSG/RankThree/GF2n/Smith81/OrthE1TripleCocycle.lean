module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

namespace Triple

variable {K : Type} [Field K]

@[expose] noncomputable def rhoLin
    (g : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    Module.End K (Matrix (Fin 2) (Fin 2) K) where
  toFun X := (g.1 : Matrix (Fin 2) (Fin 2) K) * X *
    ((g.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' r X := by simp

theorem rhoLin_apply
    (g : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (X : Matrix (Fin 2) (Fin 2) K) :
    rhoLin g X = (g.1 : Matrix (Fin 2) (Fin 2) K) * X *
      ((g.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rfl

theorem rhoLin_fst_apply (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (X : Matrix (Fin 2) (Fin 2) K) :
    rhoLin ((A, 1) : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
        X = (A : Matrix (Fin 2) (Fin 2) K) * X := by
  simp [rhoLin_apply]

theorem rhoLin_snd_apply (B : Matrix.SpecialLinearGroup (Fin 2) K)
    (X : Matrix (Fin 2) (Fin 2) K) :
    rhoLin ((1, B) : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
        X = X * ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  simp [rhoLin_apply]

theorem rhoLin_mul
    (g h : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    rhoLin (g * h) = rhoLin g * rhoLin h := by
  ext X : 1
  simp [rhoLin_apply, Matrix.mul_assoc]

theorem m2_single_eq_smul (b l : Fin 2) (c : K) :
    (Matrix.single b l c : Matrix (Fin 2) (Fin 2) K) = c • Matrix.single b l 1 := by
  simp [Matrix.smul_single]

theorem endM2_map_single_eq (m : Module.End K (Matrix (Fin 2) (Fin 2) K)) (b l : Fin 2)
    (c : K) : m (Matrix.single b l c) = c • m (Matrix.single b l 1) := by
  rw [m2_single_eq_smul, map_smul]

theorem endM2_ext_basis {m n : Module.End K (Matrix (Fin 2) (Fin 2) K)}
    (h : ∀ b l, m (Matrix.single b l 1) = n (Matrix.single b l 1)) : m = n := by
  refine Matrix.ext_linearMap K fun b l => LinearMap.ext fun c => ?_
  simp only [LinearMap.comp_apply, Matrix.singleLinearMap_apply]
  rw [endM2_map_single_eq m b l c, endM2_map_single_eq n b l c, h]

@[expose] def endBlk (m : Module.End K (Matrix (Fin 2) (Fin 2) K)) (j l : Fin 2) :
    Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun a b => m (Matrix.single b l 1) a j

theorem endBlk_apply (m : Module.End K (Matrix (Fin 2) (Fin 2) K)) (j l a b : Fin 2) :
    endBlk m j l a b = m (Matrix.single b l 1) a j := rfl

theorem endBlk_add (m n : Module.End K (Matrix (Fin 2) (Fin 2) K)) (j l : Fin 2) :
    endBlk (m + n) j l = endBlk m j l + endBlk n j l := by
  ext a b
  simp [endBlk_apply]

theorem endBlk_sub (m n : Module.End K (Matrix (Fin 2) (Fin 2) K)) (j l : Fin 2) :
    endBlk (m - n) j l = endBlk m j l - endBlk n j l := by
  ext a b
  simp [endBlk_apply]

theorem endBlk_injective {m n : Module.End K (Matrix (Fin 2) (Fin 2) K)}
    (h : ∀ j l, endBlk m j l = endBlk n j l) : m = n := by
  refine endM2_ext_basis fun b l => ?_
  ext a j
  simpa [endBlk_apply] using congrFun (congrFun (h j l) a) b

theorem endBlk_rho_mul (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (m : Module.End K (Matrix (Fin 2) (Fin 2) K)) (j l : Fin 2) :
    endBlk (rhoLin (A, 1) * m) j l = (A : Matrix (Fin 2) (Fin 2) K) * endBlk m j l := by
  ext a b
  simp [endBlk_apply, rhoLin_fst_apply, Matrix.mul_apply]

theorem m2_mul_single_eq (A : Matrix (Fin 2) (Fin 2) K) (b l : Fin 2) :
    A * Matrix.single b l (1 : K) = ∑ c, Matrix.single c l (A c b) := by
  ext i k
  fin_cases i <;> fin_cases k <;> fin_cases b <;> fin_cases l <;>
    simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two]

theorem endBlk_mul_rho (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (m : Module.End K (Matrix (Fin 2) (Fin 2) K)) (j l : Fin 2) :
    endBlk (m * rhoLin (A, 1)) j l = endBlk m j l * (A : Matrix (Fin 2) (Fin 2) K) := by
  ext a b
  rw [endBlk_apply, Module.End.mul_apply, rhoLin_fst_apply, m2_mul_single_eq, map_sum,
    Fin.sum_univ_two, endM2_map_single_eq m 0 l ((A : Matrix (Fin 2) (Fin 2) K) 0 b),
    endM2_map_single_eq m 1 l ((A : Matrix (Fin 2) (Fin 2) K) 1 b)]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, endBlk_apply]
  ring

@[expose] def endOfBlks (M : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) K) :
    Module.End K (Matrix (Fin 2) (Fin 2) K) where
  toFun X := Matrix.of fun a j => ∑ b, ∑ l, M j l a b * X b l
  map_add' X Y := by
    ext a j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' r X := by
    ext a j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply,
      Fin.sum_univ_two]
    ring

theorem endBlk_endOfBlks (M : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) K) (j l : Fin 2) :
    endBlk (endOfBlks M) j l = M j l := by
  ext a b
  fin_cases b <;> fin_cases l <;>
    simp [endBlk_apply, endOfBlks, Matrix.single_apply, Fin.sum_univ_two]

theorem kf10_specialLinear (hKF10 : H1TensorStatement) [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K)
    (c : Matrix.SpecialLinearGroup (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
    (hc : ∀ A A' : Matrix.SpecialLinearGroup (Fin 2) K, c (A * A') =
      (A : Matrix (Fin 2) (Fin 2) K) * c A' + c A * (A' : Matrix (Fin 2) (Fin 2) K)) :
    ∃ m : Matrix (Fin 2) (Fin 2) K, ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      c A = (A : Matrix (Fin 2) (Fin 2) K) * m - m * (A : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨e, he⟩ : ∃ e : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥(CFSG.Open.StatedSL 2 K),
      ∀ A, ((e A : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = A :=
    ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K, fun A => rfl⟩
  obtain ⟨m, hm⟩ := hKF10 K hK (fun g => c (e.symm g)) (by
    intro g h
    obtain ⟨A, rfl⟩ := e.surjective g
    obtain ⟨B, rfl⟩ := e.surjective h
    simpa [he, ← map_mul] using hc A B)
  refine ⟨m, fun A => ?_⟩
  simpa [he] using hm (e A)

theorem cocycle_left_coboundary (hKF10 : H1TensorStatement) [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K)
    (c0 : Matrix.SpecialLinearGroup (Fin 2) K → Module.End K (Matrix (Fin 2) (Fin 2) K))
    (hc0 : ∀ A A', c0 (A * A') = rhoLin (A, 1) * c0 A' + c0 A * rhoLin (A', 1)) :
    ∃ m : Module.End K (Matrix (Fin 2) (Fin 2) K), ∀ A,
      c0 A = rhoLin (A, 1) * m - m * rhoLin (A, 1) := by
  have h : ∀ j l, ∃ m : Matrix (Fin 2) (Fin 2) K, ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      endBlk (c0 A) j l =
        (A : Matrix (Fin 2) (Fin 2) K) * m - m * (A : Matrix (Fin 2) (Fin 2) K) := by
    intro j l
    refine kf10_specialLinear hKF10 hK (fun A => endBlk (c0 A) j l) ?_
    intro A A'
    simp only [hc0 A A', endBlk_add, endBlk_rho_mul, endBlk_mul_rho]
  choose mm hmm using h
  refine ⟨endOfBlks mm, fun A => endBlk_injective fun j l => ?_⟩
  rw [hmm j l A, endBlk_sub, endBlk_rho_mul, endBlk_mul_rho, endBlk_endOfBlks]

@[expose] def trLin : Module.End K (Matrix (Fin 2) (Fin 2) K) where
  toFun X := Xᵀ
  map_add' X Y := Matrix.transpose_add X Y
  map_smul' r X := by simp

theorem trLin_apply (X : Matrix (Fin 2) (Fin 2) K) :
    (trLin : Module.End K (Matrix (Fin 2) (Fin 2) K)) X = Xᵀ := rfl

theorem trLin_mul_self : (trLin * trLin : Module.End K (Matrix (Fin 2) (Fin 2) K)) = 1 := by
  ext X : 1
  simp [trLin_apply]

@[expose] def phiSL (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  Matrix.SpecialLinearGroup.transpose B⁻¹

theorem coe_phiSL (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((phiSL B : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ := rfl

theorem phiSL_mul (A B : Matrix.SpecialLinearGroup (Fin 2) K) :
    phiSL (A * B) = phiSL A * phiSL B := by
  apply Subtype.ext
  simp [coe_phiSL, Matrix.transpose_mul]

theorem phiSL_one : phiSL (1 : Matrix.SpecialLinearGroup (Fin 2) K) = 1 := by
  apply Subtype.ext
  simp [coe_phiSL]

@[expose] def phiSLHom :
    Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun := phiSL
  map_one' := phiSL_one
  map_mul' := phiSL_mul

theorem phiSL_inv (B : Matrix.SpecialLinearGroup (Fin 2) K) : phiSL B⁻¹ = (phiSL B)⁻¹ :=
  map_inv phiSLHom B

theorem inv_phiSL (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (phiSL A)⁻¹ = Matrix.SpecialLinearGroup.transpose A := by
  rw [← phiSL_inv]
  simp [phiSL]

theorem phiSL_phiSL (B : Matrix.SpecialLinearGroup (Fin 2) K) : phiSL (phiSL B) = B := by
  rw [phiSL, inv_phiSL]
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_transpose]

theorem trLin_comm_fst (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (trLin : Module.End K (Matrix (Fin 2) (Fin 2) K)) * rhoLin (A, 1) =
      rhoLin (1, phiSL A) * trLin := by
  ext X : 1
  simp [trLin_apply, rhoLin_fst_apply, rhoLin_snd_apply, inv_phiSL, Matrix.transpose_mul]

theorem trLin_comm_snd (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    (trLin : Module.End K (Matrix (Fin 2) (Fin 2) K)) * rhoLin (1, B) =
      rhoLin (phiSL B, 1) * trLin := by
  ext X : 1
  simp [trLin_apply, rhoLin_fst_apply, rhoLin_snd_apply, coe_phiSL, Matrix.transpose_mul]

@[expose] def conjTr (f : Module.End K (Matrix (Fin 2) (Fin 2) K)) :
    Module.End K (Matrix (Fin 2) (Fin 2) K) := trLin * f * trLin

theorem conjTr_conjTr (f : Module.End K (Matrix (Fin 2) (Fin 2) K)) :
    conjTr (conjTr f) = f := by
  have h : (trLin * trLin : Module.End K (Matrix (Fin 2) (Fin 2) K)) = 1 := trLin_mul_self
  calc conjTr (conjTr f) = (trLin * trLin) * f * (trLin * trLin) := by
        simp [conjTr, mul_assoc]
    _ = f := by rw [h]; simp

theorem conjTr_add (f g : Module.End K (Matrix (Fin 2) (Fin 2) K)) :
    conjTr (f + g) = conjTr f + conjTr g := by
  simp [conjTr, mul_add, add_mul]

theorem conjTr_sub (f g : Module.End K (Matrix (Fin 2) (Fin 2) K)) :
    conjTr (f - g) = conjTr f - conjTr g := by
  simp [conjTr, mul_sub, sub_mul]

theorem conjTr_mul (f g : Module.End K (Matrix (Fin 2) (Fin 2) K)) :
    conjTr (f * g) = conjTr f * conjTr g := by
  have h : (trLin * trLin : Module.End K (Matrix (Fin 2) (Fin 2) K)) = 1 := trLin_mul_self
  calc conjTr (f * g) = trLin * f * (trLin * trLin) * g * trLin := by
        simp [conjTr, h, mul_assoc]
    _ = conjTr f * conjTr g := by simp [conjTr, mul_assoc]

theorem conjTr_rho_fst (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    conjTr (rhoLin (A, 1) : Module.End K (Matrix (Fin 2) (Fin 2) K)) = rhoLin (1, phiSL A) := by
  have h : (trLin * trLin : Module.End K (Matrix (Fin 2) (Fin 2) K)) = 1 := trLin_mul_self
  rw [conjTr, trLin_comm_fst, mul_assoc, h, mul_one]

theorem conjTr_rho_snd (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    conjTr (rhoLin (1, B) : Module.End K (Matrix (Fin 2) (Fin 2) K)) = rhoLin (phiSL B, 1) := by
  have h : (trLin * trLin : Module.End K (Matrix (Fin 2) (Fin 2) K)) = 1 := trLin_mul_self
  rw [conjTr, trLin_comm_snd, mul_assoc, h, mul_one]

theorem cocycle_right_coboundary (hKF10 : H1TensorStatement) [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K)
    (c1 : Matrix.SpecialLinearGroup (Fin 2) K → Module.End K (Matrix (Fin 2) (Fin 2) K))
    (hc1 : ∀ B B', c1 (B * B') = rhoLin (1, B) * c1 B' + c1 B * rhoLin (1, B')) :
    ∃ m : Module.End K (Matrix (Fin 2) (Fin 2) K), ∀ B,
      c1 B = rhoLin (1, B) * m - m * rhoLin (1, B) := by
  obtain ⟨m, hm⟩ := cocycle_left_coboundary hKF10 hK (fun A => conjTr (c1 (phiSL A))) (by
    intro A A'
    simp only [phiSL_mul, hc1, conjTr_add, conjTr_mul, conjTr_rho_snd, phiSL_phiSL])
  refine ⟨conjTr m, fun B => ?_⟩
  have h := hm (phiSL B)
  rw [phiSL_phiSL] at h
  rw [← conjTr_conjTr (c1 B), h, conjTr_sub, conjTr_mul, conjTr_mul, conjTr_rho_fst,
    phiSL_phiSL]

@[expose] def lmulM2 (N : Matrix (Fin 2) (Fin 2) K) :
    Module.End K (Matrix (Fin 2) (Fin 2) K) where
  toFun X := N * X
  map_add' X Y := Matrix.mul_add N X Y
  map_smul' r X := by simp

theorem lmulM2_apply (N X : Matrix (Fin 2) (Fin 2) K) : lmulM2 N X = N * X := rfl

theorem m2_eq_four (S : Matrix (Fin 2) (Fin 2) K) :
    S = S 0 0 • Matrix.single 0 0 1 + S 0 1 • Matrix.single 0 1 1 +
      S 1 0 • Matrix.single 1 0 1 + S 1 1 • Matrix.single 1 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

theorem endM2_commutant (m : Module.End K (Matrix (Fin 2) (Fin 2) K))
    (hm : ∀ B : Matrix.SpecialLinearGroup (Fin 2) K, m * rhoLin (1, B) = rhoLin (1, B) * m) :
    ∃ N : Matrix (Fin 2) (Fin 2) K, ∀ X, m X = N * X := by
  have h1 : ∀ (S : Matrix.SpecialLinearGroup (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K),
      m (X * (S : Matrix (Fin 2) (Fin 2) K)) = m X * (S : Matrix (Fin 2) (Fin 2) K) := by
    intro S X
    have h := congrArg (fun f => f X) (hm S⁻¹)
    simpa [rhoLin_snd_apply] using h
  have hE01 : ∀ X, m (X * Matrix.single 0 1 1) = m X * Matrix.single 0 1 1 := by
    intro X
    let S : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have e : (S : Matrix (Fin 2) (Fin 2) K) = 1 + Matrix.single 0 1 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [S, Matrix.single_apply]
    have h := h1 S X
    rw [e, Matrix.mul_add, Matrix.mul_one, map_add, Matrix.mul_add, Matrix.mul_one] at h
    exact add_left_cancel h
  have hE10 : ∀ X, m (X * Matrix.single 1 0 1) = m X * Matrix.single 1 0 1 := by
    intro X
    let S : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    have e : (S : Matrix (Fin 2) (Fin 2) K) = 1 + Matrix.single 1 0 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [S, Matrix.single_apply]
    have h := h1 S X
    rw [e, Matrix.mul_add, Matrix.mul_one, map_add, Matrix.mul_add, Matrix.mul_one] at h
    exact add_left_cancel h
  have hE00 : ∀ X, m (X * Matrix.single 0 0 1) = m X * Matrix.single 0 0 1 := by
    intro X
    have e : (Matrix.single 0 0 1 : Matrix (Fin 2) (Fin 2) K) =
        Matrix.single 0 1 1 * Matrix.single 1 0 1 := by simp
    rw [e, ← Matrix.mul_assoc, hE10, hE01, Matrix.mul_assoc]
  have hE11 : ∀ X, m (X * Matrix.single 1 1 1) = m X * Matrix.single 1 1 1 := by
    intro X
    have e : (Matrix.single 1 1 1 : Matrix (Fin 2) (Fin 2) K) =
        Matrix.single 1 0 1 * Matrix.single 0 1 1 := by simp
    rw [e, ← Matrix.mul_assoc, hE01, hE10, Matrix.mul_assoc]
  have hall : ∀ X S : Matrix (Fin 2) (Fin 2) K, m (X * S) = m X * S := by
    intro X S
    conv_lhs => rw [m2_eq_four S]
    conv_rhs => rw [m2_eq_four S]
    simp only [Matrix.mul_add, map_add, Matrix.mul_smul, map_smul, hE00, hE01, hE10, hE11]
  refine ⟨Matrix.of fun a b => m (Matrix.single b 0 1) a 0, fun X => ?_⟩
  have key : ∀ b l : Fin 2, m (Matrix.single b l 1) =
      lmulM2 (Matrix.of fun a b => m (Matrix.single b 0 1) a 0) (Matrix.single b l 1) := by
    intro b l
    have e : (Matrix.single b l 1 : Matrix (Fin 2) (Fin 2) K) =
        Matrix.single b 0 1 * Matrix.single 0 l 1 := by simp
    rw [e, hall, lmulM2_apply]
    ext a j
    fin_cases l <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two]
  have := endM2_ext_basis key
  exact congrArg (fun f => f X) this

theorem cocycle_final_alg {R : Type*} [Ring R] (a b l m₀ : R) (h : l * b = b * l) :
    (a * l - l * a) * b + (a * b * m₀ - m₀ * (a * b)) =
      a * b * (m₀ + l) - (m₀ + l) * (a * b) := by
  have h1 : a * b * l = a * l * b := by rw [mul_assoc, ← h, ← mul_assoc]
  calc (a * l - l * a) * b + (a * b * m₀ - m₀ * (a * b))
      = a * l * b - l * a * b + (a * b * m₀ - m₀ * (a * b)) := by noncomm_ring
    _ = a * b * l - l * a * b + (a * b * m₀ - m₀ * (a * b)) := by rw [h1]
    _ = a * b * (m₀ + l) - (m₀ + l) * (a * b) := by noncomm_ring

theorem cocycle_coboundary (hKF10 : H1TensorStatement) [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K)
    (c : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →
      Module.End K (Matrix (Fin 2) (Fin 2) K))
    (hc : ∀ g h, c (g * h) = rhoLin g * c h + c g * rhoLin h) :
    ∃ m : Module.End K (Matrix (Fin 2) (Fin 2) K), ∀ g, c g = rhoLin g * m - m * rhoLin g := by
  obtain ⟨m₀, hm₀⟩ := cocycle_right_coboundary hKF10 hK (fun B => c (1, B)) (by
    intro B B'
    simpa [Prod.mk_mul_mk] using hc (1, B) (1, B'))
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K → Module.End K (Matrix (Fin 2) (Fin 2) K),
      ∀ g, c₁ g = c g - (rhoLin g * m₀ - m₀ * rhoLin g) := ⟨_, fun g => rfl⟩
  have hc₁ : ∀ g h, c₁ (g * h) = rhoLin g * c₁ h + c₁ g * rhoLin h := by
    intro g h
    rw [hc₁def, hc₁def, hc₁def, hc g h, rhoLin_mul]
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_assoc]
    abel
  have hc₁_right : ∀ B, c₁ (1, B) = 0 := by
    intro B
    rw [hc₁def, hm₀ B, sub_self]
  have p1 : ∀ A B : Matrix.SpecialLinearGroup (Fin 2) K,
      ((A, 1) : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) *
        (1, B) = (A, B) := by
    intro A B
    simp [Prod.mk_mul_mk]
  have p2 : ∀ A B : Matrix.SpecialLinearGroup (Fin 2) K,
      ((1, B) : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) *
        (A, 1) = (A, B) := by
    intro A B
    simp [Prod.mk_mul_mk]
  have hc₁AB : ∀ A B, c₁ (A, B) = c₁ (A, 1) * rhoLin (1, B) := by
    intro A B
    have e := hc₁ (A, 1) (1, B)
    rw [p1, hc₁_right B, mul_zero, zero_add] at e
    exact e
  have hcomm : ∀ A B, c₁ (A, 1) * rhoLin (1, B) = rhoLin (1, B) * c₁ (A, 1) := by
    intro A B
    have e := hc₁ (1, B) (A, 1)
    rw [p2, hc₁_right B, zero_mul, add_zero] at e
    exact (hc₁AB A B).symm.trans e
  choose N hN using fun A => endM2_commutant (c₁ (A, 1)) (hcomm A)
  have hNc : ∀ A A' : Matrix.SpecialLinearGroup (Fin 2) K, N (A * A') =
      (A : Matrix (Fin 2) (Fin 2) K) * N A' + N A * (A' : Matrix (Fin 2) (Fin 2) K) := by
    intro A A'
    have h := congrArg (fun f => f (1 : Matrix (Fin 2) (Fin 2) K)) (hc₁ (A, 1) (A', 1))
    simp only [Prod.mk_mul_mk, mul_one] at h
    simpa [hN, Module.End.mul_apply, rhoLin_fst_apply] using h
  obtain ⟨m₁, hm₁⟩ := kf10_specialLinear hKF10 hK N hNc
  refine ⟨m₀ + lmulM2 m₁, fun g => ?_⟩
  obtain ⟨A, B⟩ := g
  have hfac : rhoLin ((A, B) : Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) = rhoLin (A, 1) * rhoLin (1, B) := by
    rw [← rhoLin_mul, p1]
  have hc₁A : c₁ (A, 1) = rhoLin (A, 1) * lmulM2 m₁ - lmulM2 m₁ * rhoLin (A, 1) := by
    ext X : 1
    rw [hN A X, hm₁ A]
    simp [lmulM2_apply, rhoLin_fst_apply, sub_mul, Matrix.mul_assoc]
  have hlcomm : lmulM2 m₁ * rhoLin (1, B) = rhoLin (1, B) * lmulM2 m₁ := by
    ext X : 1
    simp [lmulM2_apply, rhoLin_snd_apply, Matrix.mul_assoc]
  have hg : c (A, B) = c₁ (A, B) + (rhoLin (A, B) * m₀ - m₀ * rhoLin (A, B)) := by
    rw [hc₁def]
    abel
  rw [hg, hc₁AB, hc₁A, hfac]
  exact cocycle_final_alg _ _ _ _ hlcomm

end Triple

end CFSG.RankThree.GF2n.Smith81.Smith23E1
