module

public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofSL3Mat
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeSL

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Aut

open Matrix CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat
open CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree (stdAut3 exists_std_form coe_stdAut3)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation
  slConjugation_matrix toGL_slConjugation slConjugation_scalar)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_sq
  slGraphAut_field_commute slGraphAut_matrix)

variable {K : Type} [Field K]

@[expose] def dgl (a b c : Kˣ) : GL (Fin 3) K :=
  ⟨diagonal ![(a : K), b, c], diagonal ![((a⁻¹ : Kˣ) : K), (b⁻¹ : Kˣ), (c⁻¹ : Kˣ)],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp⟩

theorem dgl_coe (a b c : Kˣ) :
    ((dgl a b c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![(a : K), b, c] :=
  rfl

theorem dgl_inv_coe (a b c : Kˣ) :
    (((dgl a b c)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![((a⁻¹ : Kˣ) : K), (b⁻¹ : Kˣ), (c⁻¹ : Kˣ)] :=
  rfl

theorem conj_eq_slConjugation (g : SpecialLinearGroup (Fin 3) K) :
    MulAut.conj g = slConjugation 3 K (SpecialLinearGroup.toGL g) := by
  ext h : 1
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_slConjugation, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem congr_conj_slConjugation (g : SpecialLinearGroup (Fin 3) K) (A : GL (Fin 3) K) :
    MulAut.congr (MulAut.conj g) (slConjugation 3 K A) =
      slConjugation 3 K (SpecialLinearGroup.toGL g * A * (SpecialLinearGroup.toGL g)⁻¹) := by
  ext h : 1
  apply SpecialLinearGroup.toGL_injective
  rw [MulAut.congr_apply]
  change SpecialLinearGroup.toGL (MulAut.conj g (slConjugation 3 K A ((MulAut.conj g).symm h))) = _
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, toGL_slConjugation, toGL_slConjugation,
    MulAut.conj_symm_apply, map_mul, map_mul, map_inv]
  group

theorem slFieldAut_mul_slConjugation_mul_inv (ρ : K ≃+* K) (A : GL (Fin 3) K) :
    slFieldAut (Fin 3) K ρ * slConjugation 3 K A * (slFieldAut (Fin 3) K ρ)⁻¹ =
      slConjugation 3 K (GeneralLinearGroup.map (ρ : K →+* K) A) := by
  ext h i j
  rw [← map_inv]
  change ρ (((slConjugation 3 K A) (slFieldAut (Fin 3) K ρ⁻¹ h) :
    SpecialLinearGroup (Fin 3) K) i j) = _
  rw [slConjugation_matrix, slConjugation_matrix]
  have hρ : ∀ M : Matrix (Fin 3) (Fin 3) K, ρ (M i j) = (M.map ρ) i j := fun M => rfl
  rw [hρ, Matrix.map_mul, Matrix.map_mul]
  have h1 : ((slFieldAut (Fin 3) K ρ⁻¹ h : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).map ρ = (h : Matrix (Fin 3) (Fin 3) K) := by
    ext k l
    change ρ (ρ⁻¹ (h k l)) = h k l
    exact ρ.apply_symm_apply (h k l)
  rw [h1]
  have h2 : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map ρ =
      (((GeneralLinearGroup.map (ρ : K →+* K) A)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
    rw [← map_inv]
    rfl
  rw [h2]
  rfl

theorem slGraphAut_mul_slConjugation_mul_inv (A : GL (Fin 3) K) :
    slGraphAut 3 K * slConjugation 3 K A * (slGraphAut 3 K)⁻¹ =
      slConjugation 3 K (GeneralLinearGroup.inverseTranspose A) := by
  have hγinv : (slGraphAut 3 K)⁻¹ = slGraphAut 3 K := by
    rw [inv_eq_of_mul_eq_one_right]
    rw [← sq, slGraphAut_sq]
  rw [hγinv]
  ext h : 1
  apply SpecialLinearGroup.toGL_injective
  change SpecialLinearGroup.toGL (slGraphAut 3 K (slConjugation 3 K A (slGraphAut 3 K h))) = _
  rw [CFSG.ComponentClassification.CatalogueBGraphForm.toGL_slGraphAut, toGL_slConjugation,
    CFSG.ComponentClassification.CatalogueBGraphForm.toGL_slGraphAut, toGL_slConjugation,
    map_mul, map_mul, map_inv,
    show CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 K
      (CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 K
        (SpecialLinearGroup.toGL h)) = SpecialLinearGroup.toGL h from
      GeneralLinearGroup.inverseTranspose_inverseTranspose _]

theorem exists_scalar_of_slConjugation_eq {A B : GL (Fin 3) K}
    (h : slConjugation 3 K A = slConjugation 3 K B) :
    ∃ c : K, ((A⁻¹ * B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c := by
  apply exists_scalar_of_commute
  intro g
  have h1 := congrArg (fun σ : MulAut (SpecialLinearGroup (Fin 3) K) =>
    ((σ g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
  simp only [slConjugation_matrix] at h1
  have hA : (A : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA' : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hB' : ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Units.val_mul]
  calc (A⁻¹ : GL (Fin 3) K).val * B.val * g
      = (A⁻¹ : GL (Fin 3) K).val * (B.val * g * (B⁻¹ : GL (Fin 3) K).val) * B.val := by
        simp only [Matrix.mul_assoc, hB', Matrix.mul_one]
    _ = (A⁻¹ : GL (Fin 3) K).val * (A.val * g * (A⁻¹ : GL (Fin 3) K).val) * B.val := by
        rw [h1]
    _ = g * ((A⁻¹ : GL (Fin 3) K).val * B.val) := by
        simp only [← Matrix.mul_assoc, hA', Matrix.one_mul]

theorem slGraphAut_pow_coe (ε : ℕ) (hε : ε ≤ 1) (g : SpecialLinearGroup (Fin 3) K) :
    (((slGraphAut 3 K ^ ε) g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      if ε = 0 then (g : Matrix (Fin 3) (Fin 3) K)
      else ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ := by
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rfl
  · rw [pow_one]
    simp only [one_ne_zero, ↓reduceIte]
    exact slGraphAut_matrix 3 K g

theorem stdAut3_mul_slConjugation_mul_inv (A : GL (Fin 3) K) (ρ : K ≃+* K) (ε : ℕ)
    (D : GL (Fin 3) K) :
    stdAut3 A ρ ε * slConjugation 3 K D * (stdAut3 A ρ ε)⁻¹ =
      slConjugation 3 K (A * GeneralLinearGroup.map (ρ : K →+* K)
        (GeneralLinearGroup.inverseTranspose^[ε] D) * A⁻¹) := by
  have hγ : ∀ m : ℕ, slGraphAut 3 K ^ m * slConjugation 3 K D * (slGraphAut 3 K ^ m)⁻¹ =
      slConjugation 3 K (GeneralLinearGroup.inverseTranspose^[m] D) := by
    intro m
    induction m generalizing D with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Function.iterate_succ_apply', ← slGraphAut_mul_slConjugation_mul_inv, ← ih]
      group
  rw [stdAut3]
  calc slConjugation 3 K A * slFieldAut (Fin 3) K ρ * slGraphAut 3 K ^ ε * slConjugation 3 K D *
        (slConjugation 3 K A * slFieldAut (Fin 3) K ρ * slGraphAut 3 K ^ ε)⁻¹
      = slConjugation 3 K A * (slFieldAut (Fin 3) K ρ * (slGraphAut 3 K ^ ε *
          slConjugation 3 K D * (slGraphAut 3 K ^ ε)⁻¹) * (slFieldAut (Fin 3) K ρ)⁻¹) *
          (slConjugation 3 K A)⁻¹ := by group
    _ = _ := by
      rw [hγ, slFieldAut_mul_slConjugation_mul_inv, ← map_inv, ← map_mul, ← map_mul]

theorem exists_scalar_mul_of_slConjugation_eq {N D : GL (Fin 3) K}
    (h : slConjugation 3 K N = slConjugation 3 K D) :
    ∃ c : K, (N : Matrix (Fin 3) (Fin 3) K) = c • (D : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨c, hc⟩ := exists_scalar_of_slConjugation_eq h.symm
  refine ⟨c, ?_⟩
  have hD : (D : Matrix (Fin 3) (Fin 3) K) * ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Units.val_mul] at hc
  calc (N : Matrix (Fin 3) (Fin 3) K)
      = (D : Matrix (Fin 3) (Fin 3) K) * (((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          N) := by rw [← Matrix.mul_assoc, hD, Matrix.one_mul]
    _ = c • (D : Matrix (Fin 3) (Fin 3) K) := by
        rw [hc, scalar_apply]
        ext i j
        rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem trace_conj_GL (A : GL (Fin 3) K) (M : Matrix (Fin 3) (Fin 3) K) :
    ((A : Matrix (Fin 3) (Fin 3) K) * M * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).trace =
      M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]

theorem det_conj_GL (A : GL (Fin 3) K) (M : Matrix (Fin 3) (Fin 3) K) :
    ((A : Matrix (Fin 3) (Fin 3) K) * M * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).det =
      M.det := by
  rw [det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, det_one, one_mul]

theorem map_iterate_dgl (ρ : K ≃+* K) (ε : ℕ) (hε : ε ≤ 1) (u : Kˣ) :
    ((GeneralLinearGroup.map (ρ : K →+* K)
      (GeneralLinearGroup.inverseTranspose^[ε] (dgl 1 u u)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
      diagonal ![1, ρ ((if ε = 0 then u else u⁻¹ : Kˣ) : K),
        ρ ((if ε = 0 then u else u⁻¹ : Kˣ) : K)] := by
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · ext i j
    rw [GeneralLinearGroup.map_apply]
    fin_cases i <;> fin_cases j <;> simp [dgl_coe]
  · ext i j
    rw [GeneralLinearGroup.map_apply, Function.iterate_one,
      GeneralLinearGroup.coe_inverseTranspose, dgl_inv_coe, diagonal_transpose]
    fin_cases i <;> fin_cases j <;> simp

theorem fix_scalar_of_commute [Finite K] [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hω0 : ω ≠ 0) {t : MulAut (SpecialLinearGroup (Fin 3) K)}
    (ht : t * slConjugation 3 K (dgl 1 (Units.mk0 ω hω0) (Units.mk0 ω hω0)) =
      slConjugation 3 K (dgl 1 (Units.mk0 ω hω0) (Units.mk0 ω hω0)) * t) :
    t (scalarSL ω (cube_eq_one_of_sq_add hω)) = scalarSL ω (cube_eq_one_of_sq_add hω) := by
  set u : Kˣ := Units.mk0 ω hω0 with hu
  obtain ⟨A, ρ, ε, hε, rfl⟩ := exists_std_form t
  have h1 : stdAut3 A ρ ε * slConjugation 3 K (dgl 1 u u) * (stdAut3 A ρ ε)⁻¹ =
      slConjugation 3 K (dgl 1 u u) := by rw [ht, mul_inv_cancel_right]
  rw [stdAut3_mul_slConjugation_mul_inv] at h1
  obtain ⟨c, hc⟩ := exists_scalar_mul_of_slConjugation_eq h1
  set M' := GeneralLinearGroup.map (ρ : K →+* K)
    (GeneralLinearGroup.inverseTranspose^[ε] (dgl 1 u u)) with hM'
  set μ : K := ρ ((if ε = 0 then u else u⁻¹ : Kˣ) : K) with hμ
  have hM'coe : (M' : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, μ, μ] := map_iterate_dgl ρ ε hε u
  have hN : ((A * M' * A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * M' * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [Units.val_mul, Units.val_mul]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have htr := congrArg Matrix.trace hc
  rw [hN, trace_conj_GL, hM'coe, Matrix.trace_smul, dgl_coe, trace_diagonal, trace_diagonal,
    Fin.sum_univ_three, Fin.sum_univ_three] at htr
  have hc1 : c = 1 := by
    have e1 : (1 : K) + μ + μ = 1 := by rw [add_assoc, ← two_mul, h2, zero_mul, add_zero]
    have e2 : ((1 : Kˣ) : K) + (u : K) + (u : K) = 1 := by
      rw [Units.val_one, add_assoc, ← two_mul, h2, zero_mul, add_zero]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at htr
    rw [e1, e2, smul_eq_mul, mul_one] at htr
    exact htr.symm
  have hdet := congrArg Matrix.det hc
  rw [hN, det_conj_GL, hM'coe, Matrix.det_smul, dgl_coe, det_diagonal, det_diagonal,
    Fin.prod_univ_three, Fin.prod_univ_three, Fintype.card_fin, hc1] at hdet
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Units.val_one, one_pow, one_mul, hu, Units.val_mk0] at hdet
  have hμω : μ = ω := sq_eq_sq_char_two (by rw [sq, sq]; exact hdet)
  have hω3 := cube_eq_one_of_sq_add hω
  have hinv3 : ω⁻¹ ^ 3 = 1 := by rw [inv_pow, hω3, inv_one]
  have hsinv : (scalarSL ω hω3)⁻¹ = scalarSL ω⁻¹ hinv3 := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    change scalar (Fin 3) ω * scalar (Fin 3) ω⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hω0, map_one]
  apply Subtype.ext
  rw [coe_stdAut3, slGraphAut_pow_coe ε hε]
  have hconj : ∀ r : K, (A : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) r *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) r := by
    intro r
    rw [← (Matrix.scalar_commute r (fun s => Commute.all r s) _).eq, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hmap : ∀ r : K, (scalar (Fin 3) r).map ρ = scalar (Fin 3) (ρ r) := by
    intro r
    rw [scalar_apply, scalar_apply, Matrix.diagonal_map (map_zero ρ)]
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · simp only [↓reduceIte]
    rw [scalarSL_coe, hmap, hconj]
    simp only [↓reduceIte, hu, Units.val_mk0] at hμ
    rw [← hμ, hμω]
  · simp only [one_ne_zero, ↓reduceIte]
    rw [hsinv, scalarSL_coe, scalar_apply, diagonal_transpose, ← scalar_apply, hmap, hconj]
    simp only [one_ne_zero, ↓reduceIte, hu, Units.val_inv_eq_inv_val, Units.val_mk0] at hμ
    rw [← hμ, hμω]
    rfl

theorem slGraphAut_mul_slFieldAut (ρ : K ≃+* K) :
    slGraphAut 3 K * slFieldAut (Fin 3) K ρ = slFieldAut (Fin 3) K ρ * slGraphAut 3 K := by
  ext g : 1
  exact slGraphAut_field_commute 3 K ρ g

theorem pow_two_pow_of_cube {ω : K} (hω3 : ω ^ 3 = 1) (k : ℕ) :
    (Even k → ω ^ (2 ^ k) = ω) ∧ (Odd k → ω ^ (2 ^ k) = ω ^ 2) := by
  induction k with
  | zero => exact ⟨fun _ => by simp, fun h => absurd h (by decide)⟩
  | succ k ih =>
    rw [pow_succ, pow_mul]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hk : Odd k := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp h)
      rw [ih.2 hk, ← pow_mul]
      calc ω ^ (2 * 2) = ω ^ 3 * ω := by ring
        _ = ω := by rw [hω3, one_mul]
    · have hk : Even k := Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp h)
      rw [ih.1 hk]

theorem ne_one_of_sq_add [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  rintro rfl
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (1 : K) ^ 2 + 1 + 1 = 1 := by
    rw [one_pow, add_assoc, ← two_mul, h2, zero_mul, add_zero]
  rw [this] at hω
  exact one_ne_zero hω

theorem sq_ne_one_of_sq_add [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 2 ≠ 1 := by
  intro h
  apply ne_one_of_sq_add hω
  have h3 := cube_eq_one_of_sq_add hω
  calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by
        rw [h, inv_one, mul_one, pow_succ, h, one_mul]
    _ = 1 := by rw [h3, h, inv_one, mul_one]

theorem ne_sq_of_sq_add [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω0 : ω ≠ 0) :
    ω ≠ ω ^ 2 := by
  intro h
  apply ne_one_of_sq_add hω
  have h2 : ω * ω = ω * 1 := by rw [← sq, ← h, mul_one]
  exact mul_left_cancel₀ hω0 h2

theorem map_slGraphAut_pow_cyc (ρ : K ≃+* K) (ε : ℕ) (hε : ε ≤ 1) :
    ((((slGraphAut 3 K ^ ε) cyc : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)).map ρ = cycMat := by
  rw [slGraphAut_pow_coe ε hε]
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · simp only [↓reduceIte, cyc_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cycMat]
  · simp only [one_ne_zero, ↓reduceIte, cyc_inv_coe, cycInvMat_transpose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cycMat]

theorem mem_zpowers_of_fix [Finite K] [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hω0 : ω ≠ 0) {σ : K ≃+* K} (hσ : ∀ a, σ a = a ^ 2) (hσgen : Subgroup.zpowers σ = ⊤)
    (hσfin : Finite (K ≃+* K)) {x : SpecialLinearGroup (Fin 3) K} {d : Fin 3 → K}
    (hxd : (x : Matrix (Fin 3) (Fin 3) K) = diagonal d) (hd : Function.Injective d)
    (hd3 : ∀ i, d i ^ 3 = 1) {α : MulAut (SpecialLinearGroup (Fin 3) K)} (hαx : α x = x)
    (hαP : α cyc = cyc)
    (hαz : α (scalarSL ω (cube_eq_one_of_sq_add hω)) = scalarSL ω (cube_eq_one_of_sq_add hω)) :
    α ∈ Subgroup.zpowers (slGraphAut 3 K * slFieldAut (Fin 3) K σ) := by
  have hω3 := cube_eq_one_of_sq_add hω
  obtain ⟨A, ρ, ε, hε, rfl⟩ := exists_std_form α
  obtain ⟨k, hk⟩ : ∃ k : ℕ, σ ^ k = ρ := by
    have h : ρ ∈ Subgroup.zpowers σ := by rw [hσgen]; exact Subgroup.mem_top ρ
    exact (mem_powers_iff_mem_zpowers.mpr h)
  have hρ : ∀ a, ρ a = a ^ (2 ^ k) := by
    intro a
    rw [← hk]
    clear hk
    induction k generalizing a with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      change (σ ^ k) (σ a) = _
      rw [ih, hσ, ← pow_mul, ← pow_succ']
  have hconj : ∀ r : K, (A : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) r *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) r := by
    intro r
    rw [← (Matrix.scalar_commute r (fun s => Commute.all r s) _).eq, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hmap : ∀ r : K, (scalar (Fin 3) r).map ρ = scalar (Fin 3) (ρ r) := by
    intro r
    rw [scalar_apply, scalar_apply, Matrix.diagonal_map (map_zero ρ)]
  set χ : K → K := fun a => ρ (if ε = 0 then a else a⁻¹) with hχ
  have hinv3 : ω⁻¹ ^ 3 = 1 := by rw [inv_pow, hω3, inv_one]
  have hχω : χ ω = ω := by
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0)
      hαz
    rw [coe_stdAut3, slGraphAut_pow_coe ε hε] at h1
    have hsinv : (scalarSL ω hω3)⁻¹ = scalarSL ω⁻¹ hinv3 := by
      apply inv_eq_of_mul_eq_one_right
      apply Subtype.ext
      change scalar (Fin 3) ω * scalar (Fin 3) ω⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hω0, map_one]
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · simp only [↓reduceIte, scalarSL_coe, hmap, hconj] at h1
      simpa [hχ] using h1
    · simp only [one_ne_zero, ↓reduceIte] at h1
      rw [hsinv, scalarSL_coe, scalar_apply, diagonal_transpose, ← scalar_apply, hmap,
        hconj] at h1
      simpa [hχ, scalarSL_coe] using h1
  have hne := ne_sq_of_sq_add hω hω0
  have hsq1 := sq_ne_one_of_sq_add hω
  have hεk : ε = k % 2 := by
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · simp only [hχ, ↓reduceIte, hρ] at hχω
      rcases Nat.even_or_odd k with hke | hko
      · exact (Nat.even_iff.mp hke).symm
      · rw [(pow_two_pow_of_cube hω3 k).2 hko] at hχω
        exact absurd hχω.symm hne
    · simp only [hχ, one_ne_zero, ↓reduceIte, hρ, inv_pow] at hχω
      rcases Nat.even_or_odd k with hke | hko
      · rw [(pow_two_pow_of_cube hω3 k).1 hke] at hχω
        exfalso
        apply hsq1
        rw [sq]
        nth_rewrite 1 [← hχω]
        exact inv_mul_cancel₀ hω0
      · exact (Nat.odd_iff.mp hko).symm
  have hχpow : ∀ j : ℕ, χ (ω ^ j) = ω ^ j := by
    intro j
    simp only [hχ] at hχω ⊢
    rcases (by omega : ε = 0 ∨ ε = 1) with h0 | h1
    · simp only [h0, ↓reduceIte] at hχω ⊢
      rw [map_pow, hχω]
    · simp only [h1, one_ne_zero, ↓reduceIte] at hχω ⊢
      rw [← inv_pow, map_pow, hχω]
  have hχd : ∀ i, χ (d i) = d i := by
    intro i
    rcases cube_root_cases hω (hd3 i) with h | h | h
    · rw [h, ← pow_zero ω, hχpow]
    · rw [h, ← pow_one ω, hχpow]
    · rw [h, hχpow]
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hxd, diagonal_pow, Matrix.SpecialLinearGroup.coe_one]
    have : d ^ 3 = 1 := funext hd3
    rw [this]
    exact diagonal_one
  have hxinv : x⁻¹ = x ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', hx3]
  have hmapx : ((((slGraphAut 3 K ^ ε) x : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)).map ρ = (x : Matrix (Fin 3) (Fin 3) K) := by
    rw [slGraphAut_pow_coe ε hε, hxd]
    rcases (by omega : ε = 0 ∨ ε = 1) with h0 | h1
    · simp only [h0, ↓reduceIte]
      rw [Matrix.diagonal_map (map_zero ρ)]
      congr 1
      funext i
      have := hχd i
      simp only [hχ, h0, ↓reduceIte] at this
      exact this
    · simp only [h1, one_ne_zero, ↓reduceIte]
      rw [hxinv, Matrix.SpecialLinearGroup.coe_pow, hxd, diagonal_pow, diagonal_transpose,
        Matrix.diagonal_map (map_zero ρ)]
      congr 1
      funext i
      have := hχd i
      simp only [hχ, h1, one_ne_zero, ↓reduceIte] at this
      change ρ (d i ^ 2) = d i
      have hdi : d i ≠ 0 := fun h => by have := hd3 i; rw [h] at this; norm_num at this
      rw [show d i ^ 2 = (d i)⁻¹ from
        eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hd3 i])]
      exact this
  have hAx : (A : Matrix (Fin 3) (Fin 3) K) * diagonal d = diagonal d * A := by
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
      hαx
    rw [coe_stdAut3, hmapx, hxd] at h1
    calc (A : Matrix (Fin 3) (Fin 3) K) * diagonal d
        = (A : Matrix (Fin 3) (Fin 3) K) * diagonal d *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A := by
          rw [Matrix.mul_assoc _ ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
            ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = diagonal d * A := by rw [h1]
  have hAdiag := eq_diagonal_of_commute hd hAx
  have hAP' : (A : Matrix (Fin 3) (Fin 3) K) * cycMat =
      (cycMat : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) := by
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
      hαP
    rw [coe_stdAut3, map_slGraphAut_pow_cyc ρ ε hε, cyc_coe] at h1
    calc (A : Matrix (Fin 3) (Fin 3) K) * cycMat
        = (A : Matrix (Fin 3) (Fin 3) K) * cycMat *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) := by
          rw [Matrix.mul_assoc _ ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
            ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = (cycMat : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) := by rw [h1]
  have hAP : diagonal (fun i => (A : Matrix (Fin 3) (Fin 3) K) i i) * cycMat =
      cycMat * diagonal (fun i => (A : Matrix (Fin 3) (Fin 3) K) i i) := by
    have h := hAP'
    rwa [hAdiag] at h
  obtain ⟨h01, h12⟩ := eq_scalar_of_diagonal_commute_cyc hAP
  have hAscal : (A : Matrix (Fin 3) (Fin 3) K) =
      scalar (Fin 3) ((A : Matrix (Fin 3) (Fin 3) K) 0 0) := by
    rw [hAdiag, scalar_apply]
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact h01.symm
    · exact (h01.trans h12).symm
  have hcA : slConjugation 3 K A = 1 := by
    ext g : 1
    apply Subtype.ext
    rw [slConjugation_matrix, MulAut.one_apply]
    calc (A : Matrix (Fin 3) (Fin 3) K) * g * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = g * ((A : Matrix (Fin 3) (Fin 3) K) *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
          rw [hAscal, (Matrix.scalar_commute _ (fun s => Commute.all _ s) _).eq,
            Matrix.mul_assoc]
      _ = g := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  refine ⟨(k : ℤ), ?_⟩
  change (slGraphAut 3 K * slFieldAut (Fin 3) K σ) ^ (k : ℤ) = stdAut3 A ρ ε
  rw [zpow_natCast, (show Commute (slGraphAut 3 K) (slFieldAut (Fin 3) K σ) from
    slGraphAut_mul_slFieldAut σ).mul_pow, ← map_pow, hk, stdAut3, hcA, one_mul,
    pow_eq_pow_mod k (slGraphAut_sq 3 K), ← hεk]
  exact ((show Commute (slGraphAut 3 K ^ ε) (slFieldAut (Fin 3) K ρ) from
    ((show Commute (slGraphAut 3 K) (slFieldAut (Fin 3) K ρ) from
      slGraphAut_mul_slFieldAut ρ).pow_left ε)).eq)

end CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Aut
