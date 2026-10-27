module

public import CFSG.LocalAnalysis.StandardType.GGHalfJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfCentralizer
public import CFSG.LocalAnalysis.StandardType.GGHalfFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

private theorem slConj_one_add_one_f2 : (1 : F2) + 1 = 0 := by
  linear_combination gf2_two

private theorem slConj_transvection_self_mul {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F2) * SpecialLinearGroup.transvection hij 1 = 1 := by
  rw [← SpecialLinearGroup.transvection_add, slConj_one_add_one_f2]
  exact SpecialLinearGroup.transvection_coeff_zero hij

private theorem slConj_omegaBlock_eq_tv_mul (n : ℕ) (k : Fin n) :
    omegaBlock n k =
      SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2) *
        SpecialLinearGroup.transvection
          ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne.symm) 1 := by
  rw [omegaBlock, ← slPerm_swap_castSucc_succ gf2_two k,
    slPerm_swap_eq_transvections gf2_two
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne,
    mul_assoc, slConj_transvection_self_mul _, mul_one]

private theorem slConj_transvection_prod_coe {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    ((SpecialLinearGroup.transvection hij (1 : F2) *
        SpecialLinearGroup.transvection hij.symm 1 : SpecialLinearGroup (Fin N) F2) :
        Matrix (Fin N) (Fin N) F2) =
      1 + Matrix.single i j (1 : F2) + Matrix.single j i 1 + Matrix.single i i 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.transvection_coe]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.single_mul_single_same, mul_one]
  abel

private theorem slConj_omegaBlock_coe (n : ℕ) (k : Fin n) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      1 + Matrix.single k.castSucc k.succ (1 : F2) + Matrix.single k.succ k.castSucc 1 +
        Matrix.single k.castSucc k.castSucc 1 := by
  rw [slConj_omegaBlock_eq_tv_mul]
  exact slConj_transvection_prod_coe _

private theorem slConj_det_rhoM : rhoM.det = 1 := by
  rw [rhoM, Matrix.det_fin_two_of]
  rw [zero_mul, one_mul, zero_sub, neg_eq_iff_add_eq_zero, slConj_one_add_one_f2]

private theorem slConj_submatrix_pow_equiv {F : Type} [Semiring F] {d d' : ℕ}
    (C : Matrix (Fin d) (Fin d) F) (e : Fin d ≃ Fin d') (m : ℕ) :
    (C.submatrix e.symm e.symm) ^ m = (C ^ m).submatrix e.symm e.symm := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Matrix.submatrix_one_equiv e.symm]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ,
      Matrix.submatrix_mul_equiv (C ^ m) C e.symm e.symm e.symm]

private theorem slConj_nsCore_submatrix_reindex {F : Type} [Field F] {d d' s r : ℕ}
    (C : Matrix (Fin d) (Fin d) F) (e : Fin d ≃ Fin d') (k : Fin s → ℕ) :
    (SLNS.nsCore (r := r) (C.submatrix e.symm e.symm) k).submatrix
        (Equiv.sumCongr (Equiv.prodCongr e (Equiv.refl (Fin s))) (Equiv.refl (Fin r)))
        (Equiv.sumCongr (Equiv.prodCongr e (Equiv.refl (Fin s))) (Equiv.refl (Fin r))) =
      SLNS.nsCore C k := by
  ext a b
  rcases a with ⟨a, j⟩ | a
  · rcases b with ⟨b, j'⟩ | b
    · simp only [SLNS.nsCore, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.prodCongr_apply, Prod.map_apply,
        Equiv.refl_apply, Matrix.blockDiagonal_apply]
      by_cases h : j = j'
      · subst h
        rw [if_pos rfl, if_pos rfl]
        rw [slConj_submatrix_pow_equiv (C := C) (e := e) (m := k j)]
        simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
      · rw [if_neg h, if_neg h]
    · simp only [SLNS.nsCore, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂,
        Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.prodCongr_apply, Prod.map_apply,
        Equiv.refl_apply, Matrix.zero_apply]
  · rcases b with ⟨b, j'⟩ | b
    · simp only [SLNS.nsCore, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁,
        Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.prodCongr_apply, Prod.map_apply,
        Equiv.refl_apply, Matrix.zero_apply]
    · simp only [SLNS.nsCore, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, Matrix.one_apply]

private theorem slConj_nsMat_submatrix_reindex {F : Type} [Field F] {n d d' s r : ℕ}
    (C : Matrix (Fin d) (Fin d) F) (ε : Fin n ≃ (Fin d × Fin s) ⊕ Fin r)
    (e : Fin d ≃ Fin d') (k : Fin s → ℕ) :
    SLNS.nsMat ε C k =
      SLNS.nsMat (ε.trans (Equiv.sumCongr (Equiv.prodCongr e (Equiv.refl (Fin s)))
        (Equiv.refl (Fin r)))) (C.submatrix e.symm e.symm) k := by
  rw [SLNS.nsMat, SLNS.nsMat]
  ext a b
  have h := congrFun (congrFun (slConj_nsCore_submatrix_reindex C e k) (ε a)) (ε b)
  simp only [Matrix.submatrix_apply] at h
  simp only [Matrix.submatrix_apply, Equiv.trans_apply]
  exact h.symm

private theorem slConj_hrho :
    (CoordSL.rootMat phi3).submatrix (finCongr rootPB_phi3_dim).symm
        (finCongr rootPB_phi3_dim).symm =
      rhoM := by
  have hmon : phi3.Monic := by
    change (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).Monic
    rw [← Polynomial.cyclotomic_three]
    exact Polynomial.cyclotomic.monic 3 F2
  have hcoeff0 : phi3.coeff 0 = 1 := by
    change (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).coeff 0 = 1
    simp
  have hcoeff1 : phi3.coeff 1 = 1 := by
    change (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).coeff 1 = 1
    simp [Polynomial.coeff_one]
  have hneg1 : (-(1 : F2)) = 1 := by
    rw [neg_eq_iff_add_eq_zero]
    exact slConj_one_add_one_f2
  have hmin : (CoordSL.rootPB phi3).minpolyGen = phi3 := by
    rw [CoordSL.rootPB, PowerBasis.minpolyGen_eq, AdjoinRoot.powerBasis_gen,
      AdjoinRoot.minpoly_root phi3_irreducible.ne_zero, hmon.leadingCoeff, inv_one,
      Polynomial.C_1, mul_one]
  have hformula : CoordSL.rootMat phi3 = Matrix.of (fun i j : Fin (CoordSL.rootPB phi3).dim =>
      if (j : ℕ) + 1 = (CoordSL.rootPB phi3).dim then
        -((CoordSL.rootPB phi3).minpolyGen.coeff (i : ℕ))
      else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) := by
    have hgen : (CoordSL.rootPB phi3).gen = AdjoinRoot.root phi3 := AdjoinRoot.powerBasis_gen _
    rw [CoordSL.rootMat, ← hgen]
    exact PowerBasis.leftMulMatrix (CoordSL.rootPB phi3)
  ext i j
  rw [Matrix.submatrix_apply, hformula, hmin]
  simp only [Matrix.of_apply]
  rw [finCongr_symm_apply_coe rootPB_phi3_dim i, finCongr_symm_apply_coe rootPB_phi3_dim j,
    rootPB_phi3_dim]
  fin_cases i <;> fin_cases j <;>
    simp [rhoM, hcoeff0, hcoeff1, hneg1]

private theorem slConj_nsCore_inl_inl {s r : ℕ} (k : Fin s → ℕ) (c d : Fin 2) (j j' : Fin s) :
    SLNS.nsCore (r := r) rhoM k (Sum.inl (c, j)) (Sum.inl (d, j')) =
      (if j = j' then (rhoM ^ k j) c d else 0) := by
  rw [SLNS.nsCore, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply]

private theorem slConj_nsCore_inl_inr {s r : ℕ} (k : Fin s → ℕ) (c : Fin 2) (j : Fin s)
    (x : Fin r) :
    SLNS.nsCore (r := r) rhoM k (Sum.inl (c, j)) (Sum.inr x) = 0 := by
  rw [SLNS.nsCore, Matrix.fromBlocks_apply₁₂]
  simp

private theorem slConj_nsCore_inr_inl {s r : ℕ} (k : Fin s → ℕ) (j : Fin s) (x : Fin r)
    (d : Fin 2) :
    SLNS.nsCore (r := r) rhoM k (Sum.inr x) (Sum.inl (d, j)) = 0 := by
  rw [SLNS.nsCore, Matrix.fromBlocks_apply₂₁]
  simp

private theorem slConj_nsCore_inr_inr {s r : ℕ} (k : Fin s → ℕ) (x y : Fin r) :
    SLNS.nsCore (r := r) rhoM k (Sum.inr x) (Sum.inr y) =
      (1 : Matrix (Fin r) (Fin r) F2) x y := by
  rw [SLNS.nsCore, Matrix.fromBlocks_apply₂₂]

private theorem slConj_nsCore_i0_i0 {s r : ℕ} (i₀ : Fin s) (c d : Fin 2) :
    SLNS.nsCore (r := r) rhoM (Pi.single i₀ 1) (Sum.inl (c, i₀)) (Sum.inl (d, i₀)) =
      rhoM c d := by
  rw [slConj_nsCore_inl_inl, if_pos rfl, Pi.single_eq_same, pow_one]

private theorem slConj_nsCore_i0_left {s r : ℕ} (i₀ : Fin s) (c : Fin 2)
    {v : (Fin 2 × Fin s) ⊕ Fin r} (hv : ∀ d : Fin 2, v ≠ Sum.inl (d, i₀)) :
    SLNS.nsCore (r := r) rhoM (Pi.single i₀ 1) (Sum.inl (c, i₀)) v = 0 := by
  rcases v with ⟨d, j⟩ | x
  · by_cases hj : j = i₀
    · exfalso; exact hv d (by rw [hj])
    · rw [slConj_nsCore_inl_inl, if_neg (Ne.symm hj)]
  · rw [slConj_nsCore_inl_inr]

private theorem slConj_nsCore_i0_right {s r : ℕ} (i₀ : Fin s) (d : Fin 2)
    {u : (Fin 2 × Fin s) ⊕ Fin r} (hu : ∀ c : Fin 2, u ≠ Sum.inl (c, i₀)) :
    SLNS.nsCore (r := r) rhoM (Pi.single i₀ 1) u (Sum.inl (d, i₀)) = 0 := by
  rcases u with ⟨c, j⟩ | x
  · by_cases hj : j = i₀
    · exfalso; exact hu c (by rw [hj])
    · rw [slConj_nsCore_inl_inl, if_neg hj]
  · rw [slConj_nsCore_inr_inl]

private theorem slConj_nsCore_notblock {s r : ℕ} (i₀ : Fin s)
    {u v : (Fin 2 × Fin s) ⊕ Fin r} (hu : ∀ c : Fin 2, u ≠ Sum.inl (c, i₀))
    (hv : ∀ c : Fin 2, v ≠ Sum.inl (c, i₀)) :
    SLNS.nsCore (r := r) rhoM (Pi.single i₀ 1) u v = if u = v then 1 else 0 := by
  rcases u with ⟨c, j⟩ | x <;> rcases v with ⟨d, j'⟩ | y
  · have hj : j ≠ i₀ := fun h => hu c (by rw [h])
    have hj' : j' ≠ i₀ := fun h => hv d (by rw [h])
    rw [slConj_nsCore_inl_inl]
    by_cases hjj : j = j'
    · subst hjj
      rw [if_pos rfl, Pi.single_eq_of_ne' (Ne.symm hj), pow_zero]
      by_cases hcd : c = d
      · subst hcd; simp
      · rw [Matrix.one_apply, if_neg hcd]
        rw [if_neg]
        intro h
        exact hcd (Prod.ext_iff.mp (Sum.inl.inj h)).1
    · rw [if_neg hjj]
      rw [if_neg]
      intro h
      exact hjj (Prod.ext_iff.mp (Sum.inl.inj h)).2
  · rw [slConj_nsCore_inl_inr]
    rw [if_neg]
    intro h
    exact (by cases h)
  · rw [slConj_nsCore_inr_inl]
    rw [if_neg]
    intro h
    exact (by cases h)
  · rw [slConj_nsCore_inr_inr, Matrix.one_apply]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [if_neg hxy]
      rw [if_neg]
      intro h
      exact hxy (Sum.inr.inj h)

private theorem slConj_rhs_cc {n : ℕ} (k : Fin n) :
    (1 + Matrix.single k.castSucc k.succ (1 : F2) + Matrix.single k.succ k.castSucc 1 +
      Matrix.single k.castSucc k.castSucc 1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
        k.castSucc k.castSucc = 0 := by
  have h : (k.castSucc : Fin (n + 1)) ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, h, Ne.symm h]
  linear_combination gf2_two

private theorem slConj_rhs_cs {n : ℕ} (k : Fin n) :
    (1 + Matrix.single k.castSucc k.succ (1 : F2) + Matrix.single k.succ k.castSucc 1 +
      Matrix.single k.castSucc k.castSucc 1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
        k.castSucc k.succ = 1 := by
  have h : (k.castSucc : Fin (n + 1)) ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, h, Ne.symm h]

private theorem slConj_rhs_sc {n : ℕ} (k : Fin n) :
    (1 + Matrix.single k.castSucc k.succ (1 : F2) + Matrix.single k.succ k.castSucc 1 +
      Matrix.single k.castSucc k.castSucc 1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
        k.succ k.castSucc = 1 := by
  have h : (k.castSucc : Fin (n + 1)) ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, h, Ne.symm h]

private theorem slConj_rhs_ss {n : ℕ} (k : Fin n) :
    (1 + Matrix.single k.castSucc k.succ (1 : F2) + Matrix.single k.succ k.castSucc 1 +
      Matrix.single k.castSucc k.castSucc 1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
        k.succ k.succ = 1 := by
  have h : (k.castSucc : Fin (n + 1)) ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, h, Ne.symm h]

private theorem slConj_rhs_cc_not {n : ℕ} (k : Fin n) {b : Fin (n + 1)}
    (hb0 : b ≠ k.castSucc) (hb1 : b ≠ k.succ) :
    (1 + Matrix.single k.castSucc k.succ (1 : F2) + Matrix.single k.succ k.castSucc 1 +
      Matrix.single k.castSucc k.castSucc 1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
        k.castSucc b = 0 := by
  have h : (k.castSucc : Fin (n + 1)) ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, h, Ne.symm h, hb0, hb1,
    Ne.symm hb0, Ne.symm hb1]

private theorem slConj_rhs_sc_not {n : ℕ} (k : Fin n) {b : Fin (n + 1)}
    (hb0 : b ≠ k.castSucc) (hb1 : b ≠ k.succ) :
    (1 + Matrix.single k.castSucc k.succ (1 : F2) + Matrix.single k.succ k.castSucc 1 +
      Matrix.single k.castSucc k.castSucc 1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
        k.succ b = 0 := by
  have h : (k.castSucc : Fin (n + 1)) ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, h, Ne.symm h, hb0, hb1,
    Ne.symm hb0, Ne.symm hb1]

private theorem slConj_rhs_not_cc {n : ℕ} (k : Fin n) {a : Fin (n + 1)}
    (ha0 : a ≠ k.castSucc) (ha1 : a ≠ k.succ) :
    (1 + Matrix.single k.castSucc k.succ (1 : F2) + Matrix.single k.succ k.castSucc 1 +
      Matrix.single k.castSucc k.castSucc 1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
        a k.castSucc = 0 := by
  have h : (k.castSucc : Fin (n + 1)) ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, h, Ne.symm h, ha0, ha1,
    Ne.symm ha0, Ne.symm ha1]

private theorem slConj_rhs_not_sc {n : ℕ} (k : Fin n) {a : Fin (n + 1)}
    (ha0 : a ≠ k.castSucc) (ha1 : a ≠ k.succ) :
    (1 + Matrix.single k.castSucc k.succ (1 : F2) + Matrix.single k.succ k.castSucc 1 +
      Matrix.single k.castSucc k.castSucc 1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
        a k.succ = 0 := by
  have h : (k.castSucc : Fin (n + 1)) ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, h, Ne.symm h, ha0, ha1,
    Ne.symm ha0, Ne.symm ha1]

private theorem slConj_rhs_not {n : ℕ} (k : Fin n) {a b : Fin (n + 1)}
    (ha0 : a ≠ k.castSucc) (ha1 : a ≠ k.succ) (hb0 : b ≠ k.castSucc) (hb1 : b ≠ k.succ) :
    (1 + Matrix.single k.castSucc k.succ (1 : F2) + Matrix.single k.succ k.castSucc 1 +
      Matrix.single k.castSucc k.castSucc 1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) a b =
      (if a = b then 1 else 0) := by
  have h : (k.castSucc : Fin (n + 1)) ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
  by_cases hab : a = b
  · subst hab
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, ha0, ha1, h, Ne.symm h,
      Ne.symm ha0, Ne.symm ha1]
  · simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, ha0, ha1, hb0, hb1, h,
      Ne.symm h, Ne.symm ha0, Ne.symm ha1, Ne.symm hb0, Ne.symm hb1, hab]

private theorem slConj_slPerm_inv_mul_mul_coe {N : ℕ} (π : Equiv.Perm (Fin N))
    (M : Matrix (Fin N) (Fin N) F2) :
    (((slPerm gf2_two π)⁻¹ : SpecialLinearGroup (Fin N) F2) : Matrix (Fin N) (Fin N) F2) * M *
        (slPerm gf2_two π : Matrix (Fin N) (Fin N) F2) = M.submatrix π π := by
  rw [← map_inv]
  rw [coe_slPerm, coe_slPerm, signedPerm_one_eq_permMatrix, signedPerm_one_eq_permMatrix]
  simp only [inv_inv]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rw [Matrix.submatrix_submatrix]
  rfl

theorem GGHalfJoin.exists_conj_omegaBlock_of_supp_two {m : ℕ}
    {a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2} (ha3 : a ^ 3 = 1) (hs : GGHalf.supp a = 2) :
    ∃ A : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2,
      A⁻¹ * a * A = omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩ := by
  classical
  obtain ⟨s, r, ε, A₀, k, htk⟩ := exists_frame_of_pow_three a ha3
  obtain ⟨M, k', hMk, hk'⟩ := exists_conj_nsSL_binary ε k
  have hbin : ∀ i, k' i = 0 ∨ k' i = 1 := fun i => (hk' i).1
  set Y' : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := SLNS.nsSL ε det_rootMat_phi3 k'
    with hY'def
  set A₁ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := A₀ * M with hA₁
  have hY : SLNS.nsSL ε det_rootMat_phi3 k = M * Y' * M⁻¹ := by
    rw [← hMk]; group
  have ha : a = A₁ * Y' * A₁⁻¹ := by
    rw [htk, hY, hA₁]; group
  have hsupp : 2 * (Finset.univ.filter fun i : Fin s => k' i % 3 ≠ 0).card = 2 := by
    have h1 : GGHalf.supp a = GGHalf.supp Y' := by rw [ha, GGHalf.supp_conj]
    rw [h1, GGHalf.supp_nsSL] at hs
    exact hs
  have hcard : (Finset.univ.filter fun i : Fin s => k' i % 3 ≠ 0).card = 1 := by omega
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hcard
  have hk'_single : k' = Pi.single i₀ 1 := by
    have hmem : ∀ i : Fin s,
        i ∈ (Finset.univ.filter fun i : Fin s => k' i % 3 ≠ 0) ↔ i = i₀ := by
      intro i; rw [hi₀]; simp
    have hiff : ∀ i : Fin s, k' i = 1 ↔ i = i₀ := by
      intro i
      constructor
      · intro h1
        exact (hmem i).mp (Finset.mem_filter.mpr ⟨Finset.mem_univ i, by rw [h1]; decide⟩)
      · intro hi
        have hne : k' i % 3 ≠ 0 := (Finset.mem_filter.mp ((hmem i).mpr hi)).2
        rcases hbin i with h0 | h1
        · rw [h0] at hne; simp at hne
        · exact h1
    funext i
    by_cases hi : i = i₀
    · rw [hi, Pi.single_eq_same]
      exact (hiff i₀).mpr rfl
    · rw [Pi.single_eq_of_ne' (Ne.symm hi)]
      rcases hbin i with h0 | h1
      · exact h0
      · exact absurd ((hiff i).mp h1) hi
  let ε₂ : Fin (m + 1 + 1 + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r :=
    ε.trans (Equiv.sumCongr (Equiv.prodCongr (finCongr rootPB_phi3_dim) (Equiv.refl (Fin s)))
      (Equiv.refl (Fin r)))
  have hY'mat : (Y' : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) =
      SLNS.nsMat ε₂ rhoM k' := by
    rw [hY'def]
    change SLNS.nsMat ε (CoordSL.rootMat phi3) k' = SLNS.nsMat ε₂ rhoM k'
    rw [slConj_nsMat_submatrix_reindex (ε := ε) (C := CoordSL.rootMat phi3)
      (e := finCongr rootPB_phi3_dim) (k := k')]
    rw [slConj_hrho]
  let k0 : Fin (m + 1 + 1) := ⟨0, Nat.succ_pos _⟩
  let p₀ : Fin (m + 1 + 1 + 1) := ε₂.symm (Sum.inl ((0 : Fin 2), i₀))
  let p₁ : Fin (m + 1 + 1 + 1) := ε₂.symm (Sum.inl ((1 : Fin 2), i₀))
  have hp : p₀ ≠ p₁ := by
    intro h
    have h' : (Sum.inl ((0 : Fin 2), i₀) : (Fin 2 × Fin s) ⊕ Fin r) =
        Sum.inl ((1 : Fin 2), i₀) := by
      have := congrArg ε₂ h
      simpa only [p₀, p₁, Equiv.apply_symm_apply] using this
    simp at h'
  let τ : Equiv.Perm (Fin (m + 1 + 1 + 1)) := Equiv.swap k0.castSucc p₀
  let π : Equiv.Perm (Fin (m + 1 + 1 + 1)) := τ * Equiv.swap k0.succ (τ p₁)
  have hij : k0.castSucc ≠ k0.succ := (Fin.castSucc_lt_succ (i := k0)).ne
  have hq : τ p₁ ≠ k0.castSucc := by
    have hτ : τ k0.castSucc = p₀ := Equiv.swap_apply_left _ _
    intro h
    rcases eq_or_ne p₁ k0.castSucc with hp1 | hp1
    · rw [hp1] at h
      rw [hτ] at h
      exact hp (h.trans hp1.symm)
    · rw [show τ p₁ = p₁ from Equiv.swap_apply_of_ne_of_ne hp1 hp.symm] at h
      exact hp1 h
  have hπi : π k0.castSucc = p₀ := by
    show (τ * Equiv.swap k0.succ (τ p₁)) k0.castSucc = p₀
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij (Ne.symm hq),
      show τ k0.castSucc = p₀ from Equiv.swap_apply_left _ _]
  have hπj : π k0.succ = p₁ := by
    show (τ * Equiv.swap k0.succ (τ p₁)) k0.succ = p₁
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    simpa only [τ, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
      congrArg (fun f : Equiv.Perm (Fin (m + 1 + 1 + 1)) => f p₁)
        (Equiv.swap_mul_self k0.castSucc p₀)
  have hnot : ∀ {x : Fin (m + 1 + 1 + 1)}, x ≠ k0.castSucc → x ≠ k0.succ →
      ∀ c : Fin 2, ε₂ (π x) ≠ Sum.inl (c, i₀) := by
    intro x hx0 hx1 c hc
    have hpx : π x = ε₂.symm (Sum.inl (c, i₀)) := by rw [← hc, Equiv.symm_apply_apply]
    have : x = k0.castSucc ∨ x = k0.succ := by
      fin_cases c
      · left
        refine Equiv.injective π ?_
        rw [hpx]
        simpa [p₀] using hπi.symm
      · right
        refine Equiv.injective π ?_
        rw [hpx]
        simpa [p₁] using hπj.symm
    exact this.elim hx0 hx1
  have hconj : ((slPerm gf2_two π)⁻¹ * Y' * slPerm gf2_two π :
      SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) =
      omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩ := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [slConj_slPerm_inv_mul_mul_coe (π := π) (M := (Y' : Matrix _ _ F2))]
    rw [hY'mat, hk'_single]
    rw [show (⟨0, Nat.succ_pos _⟩ : Fin (m + 1 + 1)) = k0 from rfl]
    rw [slConj_omegaBlock_coe]
    ext a b
    rw [Matrix.submatrix_apply, SLNS.nsMat, Matrix.submatrix_apply]
    by_cases ha0 : a = k0.castSucc
    · subst ha0
      rw [hπi]
      simp only [p₀, Equiv.apply_symm_apply]
      by_cases hb0 : b = k0.castSucc
      · subst hb0
        rw [hπi]
        simp only [p₀, Equiv.apply_symm_apply]
        rw [slConj_nsCore_i0_i0, slConj_rhs_cc]
        simp [rhoM]
      · by_cases hb1 : b = k0.succ
        · subst hb1
          rw [hπj]
          simp only [p₁, Equiv.apply_symm_apply]
          rw [slConj_nsCore_i0_i0, slConj_rhs_cs]
          simp [rhoM]
        · rw [slConj_nsCore_i0_left i₀ 0 (hnot hb0 hb1), slConj_rhs_cc_not (k := k0) hb0 hb1]
    · by_cases ha1 : a = k0.succ
      · subst ha1
        rw [hπj]
        simp only [p₁, Equiv.apply_symm_apply]
        by_cases hb0 : b = k0.castSucc
        · subst hb0
          rw [hπi]
          simp only [p₀, Equiv.apply_symm_apply]
          rw [slConj_nsCore_i0_i0, slConj_rhs_sc]
          simp [rhoM]
        · by_cases hb1 : b = k0.succ
          · subst hb1
            rw [hπj]
            simp only [p₁, Equiv.apply_symm_apply]
            rw [slConj_nsCore_i0_i0, slConj_rhs_ss]
            simp [rhoM]
          · rw [slConj_nsCore_i0_left i₀ 1 (hnot hb0 hb1), slConj_rhs_sc_not (k := k0) hb0 hb1]
      · by_cases hb0 : b = k0.castSucc
        · subst hb0
          rw [hπi]
          simp only [p₀, Equiv.apply_symm_apply]
          rw [slConj_nsCore_i0_right i₀ 0 (hnot ha0 ha1), slConj_rhs_not_cc (k := k0) ha0 ha1]
        · by_cases hb1 : b = k0.succ
          · subst hb1
            rw [hπj]
            simp only [p₁, Equiv.apply_symm_apply]
            rw [slConj_nsCore_i0_right i₀ 1 (hnot ha0 ha1), slConj_rhs_not_sc (k := k0) ha0 ha1]
          · rw [slConj_nsCore_notblock i₀ (hnot ha0 ha1) (hnot hb0 hb1),
                slConj_rhs_not (k := k0) ha0 ha1 hb0 hb1]
            congr 1
            simp only [ε₂.injective.eq_iff, π.injective.eq_iff]
  refine ⟨A₁ * slPerm gf2_two π, ?_⟩
  calc (A₁ * slPerm gf2_two π)⁻¹ * a * (A₁ * slPerm gf2_two π)
      = (slPerm gf2_two π)⁻¹ * Y' * slPerm gf2_two π := by
        rw [ha]; group
    _ = omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩ := hconj

end CFSG.StandardType

end
