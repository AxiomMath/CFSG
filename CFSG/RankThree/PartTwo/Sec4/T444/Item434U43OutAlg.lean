module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Code

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemU43

open CFSG.LieType.Multipliers.U43 Matrix

local notation "Mat4" => Matrix (Fin 4) (Fin 4) F9

@[expose] def cjF9 : F9 →+* F9 where
  toFun x := x ^ 3
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

theorem cjF9_apply (x : F9) : cjF9 x = x ^ 3 := rfl

theorem commutant_eq_poly {K : Type*} [Field K] (m : Fin 4 → Matrix (Fin 4) (Fin 4) K)
    (hm : ∀ i j, m i * m j = m j * m i) (e : Fin 4 → K) (Qinv : Matrix (Fin 4) (Fin 4) K)
    (hQ2 : Matrix.of (fun r j => (m j *ᵥ e) r) * Qinv = 1)
    {M : Matrix (Fin 4) (Fin 4) K} (hM : ∀ i, M * m i = m i * M) :
    M = (Qinv *ᵥ (M *ᵥ e)) 0 • m 0 + (Qinv *ᵥ (M *ᵥ e)) 1 • m 1 +
      (Qinv *ᵥ (M *ᵥ e)) 2 • m 2 + (Qinv *ᵥ (M *ᵥ e)) 3 • m 3 := by
  set Q : Matrix (Fin 4) (Fin 4) K := Matrix.of (fun r j => (m j *ᵥ e) r) with hQ
  set x := Qinv *ᵥ (M *ᵥ e) with hx
  set P : Matrix (Fin 4) (Fin 4) K := x 0 • m 0 + x 1 • m 1 + x 2 • m 2 + x 3 • m 3 with hP
  have hQcol : ∀ y : Fin 4 → K, Q *ᵥ y = y 0 • (m 0 *ᵥ e) + y 1 • (m 1 *ᵥ e) +
      y 2 • (m 2 *ᵥ e) + y 3 • (m 3 *ᵥ e) := by
    intro y
    funext r
    simp [hQ, Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm]
  have hw : M *ᵥ e = x 0 • (m 0 *ᵥ e) + x 1 • (m 1 *ᵥ e) + x 2 • (m 2 *ᵥ e) +
      x 3 • (m 3 *ᵥ e) := by
    rw [← hQcol, hx, Matrix.mulVec_mulVec, hQ2, Matrix.one_mulVec]
  have hbasis : ∀ j, M *ᵥ (m j *ᵥ e) = P *ᵥ (m j *ᵥ e) := by
    intro j
    rw [Matrix.mulVec_mulVec, hM j, ← Matrix.mulVec_mulVec, hw]
    simp only [hP, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.add_mul,
      Matrix.smul_mul, Matrix.add_mulVec, Matrix.smul_mulVec]
    rw [hm j 0, hm j 1, hm j 2, hm j 3]
  have hall : ∀ u, M *ᵥ u = P *ᵥ u := by
    intro u
    have : u = Q *ᵥ (Qinv *ᵥ u) := by rw [Matrix.mulVec_mulVec, hQ2, Matrix.one_mulVec]
    rw [this, hQcol]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hbasis]
  exact Matrix.ext_of_mulVec_single (fun i => hall _)

@[expose] def mAlg (a b : Mat4) : Fin 4 → Mat4 := ![1, a - 1, b - 1, (a - 1) * (b - 1)]

@[expose] def qAlg (a b : Mat4) : Mat4 :=
  Matrix.of fun r j => (mAlg a b j *ᵥ ![0, 0, 0, 1]) r

@[expose] def conjVec (u : Fin 4 → F9) : Fin 4 → F9 := fun k => u k ^ 3

@[expose] def OutGood (z a b Qinv T Tinv : Mat4) (u : Fin 4 → F9) : Prop :=
  (∀ i j, mAlg a b i * mAlg a b j = mAlg a b j * mAlg a b i) ∧
  z * a = a * z ∧ z * b = b * z ∧
  qAlg a b * Qinv = 1 ∧ Qinv * qAlg a b = 1 ∧
  (∀ i : Fin 4, 1 ≤ (i : ℕ) → ∀ r s : Fin 4, r ≤ s → (Qinv * mAlg a b i * qAlg a b) r s = 0) ∧
  (∀ i : Fin 4, 1 ≤ (i : ℕ) → mAlg a b i *ᵥ u = 0 ∧ conjVec u ᵥ* mAlg a b i = 0) ∧
  conjVec u ⬝ᵥ ![1, 0, 0, 0] ≠ 0 ∧
  T * a = a.map (· ^ 3) * T ∧ T * b = b.map (· ^ 3) * T ∧ T * Tinv = 1 ∧
  Tinv * z.map (· ^ 3) * T - z ≠ 0

instance (z a b Qinv T Tinv : Mat4) (u : Fin 4 → F9) :
    Decidable (OutGood z a b Qinv T Tinv u) := by
  unfold OutGood
  infer_instance

theorem comm_mAlg {a b M : Mat4} (hMa : M * a = a * M) (hMb : M * b = b * M) (i : Fin 4) :
    M * mAlg a b i = mAlg a b i * M := by
  have h1 : M * (a - 1) = (a - 1) * M := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hMa, Matrix.mul_one, Matrix.one_mul]
  have h2 : M * (b - 1) = (b - 1) * M := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hMb, Matrix.mul_one, Matrix.one_mul]
  fin_cases i
  · simp [mAlg]
  · simpa [mAlg] using h1
  · simpa [mAlg] using h2
  · simp only [mAlg]
    change M * ((a - 1) * (b - 1)) = ((a - 1) * (b - 1)) * M
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, h2, Matrix.mul_assoc]

theorem plain_det {z a b Qinv T Tinv : Mat4} {u : Fin 4 → F9}
    (hg : OutGood z a b Qinv T Tinv u) {M : Mat4} (hMa : M * a = a * M) (hMb : M * b = b * M)
    (hMu : (M.map (· ^ 3))ᵀ * M = 1) : M.det = 1 := by
  obtain ⟨hm, -, -, hQ2, hQ1, htri, hsoc, hw, -⟩ := hg
  have hM := comm_mAlg hMa hMb
  have hP := commutant_eq_poly (mAlg a b) hm ![0, 0, 0, 1] Qinv hQ2 hM
  set x := Qinv *ᵥ (M *ᵥ ![0, 0, 0, 1]) with hx
  have hm0 : mAlg a b 0 = 1 := by simp [mAlg]
  have hMN : M = x 0 • (1 : Mat4) +
      (x 1 • mAlg a b 1 + x 2 • mAlg a b 2 + x 3 • mAlg a b 3) := by
    calc M = x 0 • mAlg a b 0 + x 1 • mAlg a b 1 + x 2 • mAlg a b 2 + x 3 • mAlg a b 3 := hP
      _ = _ := by rw [hm0]; abel
  have hR : ∀ r s : Fin 4, r ≤ s → (Qinv * M * qAlg a b) r s = x 0 * (1 : Mat4) r s := by
    intro r s hrs
    have e : Qinv * M * qAlg a b = x 0 • (Qinv * qAlg a b) + (x 1 • (Qinv * mAlg a b 1 * qAlg a b) +
        x 2 • (Qinv * mAlg a b 2 * qAlg a b) + x 3 • (Qinv * mAlg a b 3 * qAlg a b)) := by
      conv_lhs => rw [hMN]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [e, hQ1]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [htri 1 (by decide) r s hrs, htri 2 (by decide) r s hrs, htri 3 (by decide) r s hrs]
    simp
  have hlow : (Qinv * M * qAlg a b).IsLowerTriangular := by
    intro i j hij
    have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
    rw [hR i j hlt.le]
    simp [Matrix.one_apply_ne hlt.ne]
  have hdetR : (Qinv * M * qAlg a b).det = x 0 ^ 4 := by
    rw [Matrix.det_of_isLowerTriangular _ hlow]
    simp [hR _ _ le_rfl]
  have hdetMR : (Qinv * M * qAlg a b).det = M.det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    have : (qAlg a b).det * Qinv.det = 1 := by rw [← Matrix.det_mul, hQ2, Matrix.det_one]
    calc Qinv.det * M.det * (qAlg a b).det = M.det * ((qAlg a b).det * Qinv.det) := by ring
      _ = M.det := by rw [this, mul_one]
  have hx4 : x 0 ^ 4 = 1 := by
    have hMu0 : M *ᵥ u = x 0 • u := by
      have : M *ᵥ u = (x 0 • (1 : Mat4) +
          (x 1 • mAlg a b 1 + x 2 • mAlg a b 2 + x 3 • mAlg a b 3)) *ᵥ u := by rw [← hMN]
      rw [this]
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        (hsoc 1 (by decide)).1, (hsoc 2 (by decide)).1, (hsoc 3 (by decide)).1, smul_zero,
        add_zero]
    have hℓM : conjVec u ᵥ* M = x 0 • conjVec u := by
      have : conjVec u ᵥ* M = conjVec u ᵥ* (x 0 • (1 : Mat4) +
          (x 1 • mAlg a b 1 + x 2 • mAlg a b 2 + x 3 • mAlg a b 3)) := by rw [← hMN]
      rw [this]
      simp only [Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_one,
        (hsoc 1 (by decide)).2, (hsoc 2 (by decide)).2, (hsoc 3 (by decide)).2, smul_zero,
        add_zero]
    have h2 : conjVec u ᵥ* (M.map (· ^ 3))ᵀ = x 0 ^ 3 • conjVec u := by
      rw [Matrix.vecMul_transpose]
      funext i
      have h := RingHom.map_mulVec cjF9 M u i
      rw [hMu0] at h
      have h' : (M.map (· ^ 3) *ᵥ conjVec u) i = x 0 ^ 3 * u i ^ 3 := by
        have := h.symm
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, cjF9_apply] at this
        exact this
      exact h'
    set ℓ := conjVec u with hℓ
    set w : Fin 4 → F9 := ![1, 0, 0, 0] with hwdef
    have h1 : ℓ ⬝ᵥ w = (x 0 ^ 3 • ℓ) ⬝ᵥ (M *ᵥ w) := by
      calc ℓ ⬝ᵥ w = ℓ ⬝ᵥ ((1 : Mat4) *ᵥ w) := by rw [Matrix.one_mulVec]
        _ = ℓ ⬝ᵥ (((M.map (· ^ 3))ᵀ * M) *ᵥ w) := by rw [hMu]
        _ = ℓ ⬝ᵥ ((M.map (· ^ 3))ᵀ *ᵥ (M *ᵥ w)) := by rw [Matrix.mulVec_mulVec]
        _ = (ℓ ᵥ* (M.map (· ^ 3))ᵀ) ⬝ᵥ (M *ᵥ w) := Matrix.dotProduct_mulVec _ _ _
        _ = (x 0 ^ 3 • ℓ) ⬝ᵥ (M *ᵥ w) := by rw [h2]
    have h3 : ℓ ⬝ᵥ (M *ᵥ w) = x 0 * (ℓ ⬝ᵥ w) := by
      rw [Matrix.dotProduct_mulVec, hℓM, smul_dotProduct, smul_eq_mul]
    rw [smul_dotProduct, smul_eq_mul, h3] at h1
    have h4 : (x 0 ^ 4 - 1) * (ℓ ⬝ᵥ w) = 0 := by linear_combination -h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right hw)
  rw [← hdetMR, hdetR, hx4]

theorem twisted_false {z a b Qinv T Tinv : Mat4} {u : Fin 4 → F9}
    (hg : OutGood z a b Qinv T Tinv u) {M : Mat4} (hMa : M * a.map (· ^ 3) = a * M)
    (hMb : M * b.map (· ^ 3) = b * M) (hMz : M * z.map (· ^ 3) = z * M) (hdet : M.det ≠ 0) :
    False := by
  obtain ⟨hm, hza, hzb, hQ2, -, -, -, -, hTa, hTb, hTT, hY⟩ := hg
  have hM'a : M * T * a = a * (M * T) := by
    rw [Matrix.mul_assoc, hTa, ← Matrix.mul_assoc, hMa, Matrix.mul_assoc]
  have hM'b : M * T * b = b * (M * T) := by
    rw [Matrix.mul_assoc, hTb, ← Matrix.mul_assoc, hMb, Matrix.mul_assoc]
  have hM' := comm_mAlg hM'a hM'b
  have hP := commutant_eq_poly (mAlg a b) hm ![0, 0, 0, 1] Qinv hQ2 hM'
  set x := Qinv *ᵥ ((M * T) *ᵥ ![0, 0, 0, 1]) with hx
  have hcz : ∀ i, Commute z (mAlg a b i) := fun i => (comm_mAlg hza hzb i :)
  have hPcomm : Commute z (M * T) := by
    rw [hP]
    exact ((((hcz 0).smul_right _).add_right ((hcz 1).smul_right _)).add_right
      ((hcz 2).smul_right _)).add_right ((hcz 3).smul_right _)
  have hPY : (M * T) * (Tinv * z.map (· ^ 3) * T - z) = 0 := by
    have h1 : (M * T) * (Tinv * z.map (· ^ 3) * T) = z * (M * T) := by
      calc (M * T) * (Tinv * z.map (· ^ 3) * T) = M * (T * Tinv) * z.map (· ^ 3) * T := by
            simp only [Matrix.mul_assoc]
        _ = M * z.map (· ^ 3) * T := by rw [hTT, Matrix.mul_one]
        _ = z * M * T := by rw [hMz]
        _ = z * (M * T) := by rw [Matrix.mul_assoc]
    rw [Matrix.mul_sub, h1]
    exact sub_eq_zero.mpr hPcomm.eq
  obtain ⟨r, c, hrc⟩ : ∃ r c, (Tinv * z.map (· ^ 3) * T - z) r c ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hY (Matrix.ext fun r c => hall r c)
  have hv : (M * T) *ᵥ (fun s => (Tinv * z.map (· ^ 3) * T - z) s c) = 0 := by
    have h0 : (M * T) *ᵥ ((Tinv * z.map (· ^ 3) * T - z) *ᵥ Pi.single c 1) = 0 := by
      rw [Matrix.mulVec_mulVec, hPY, Matrix.zero_mulVec]
    have hcol : (Tinv * z.map (· ^ 3) * T - z) *ᵥ Pi.single c 1 =
        fun s => (Tinv * z.map (· ^ 3) * T - z) s c := by
      funext s
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hcol] at h0
    exact h0
  have hdetP : (M * T).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, fun h => hrc (congrFun h r), hv⟩
  have hdetT : T.det ≠ 0 := fun h => by
    have := congrArg Matrix.det hTT
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [Matrix.det_mul] at hdetP
  exact hdet ((mul_eq_zero.mp hdetP).resolve_right hdetT)

end CFSG.RankThree.PartTwo.Sec4.Item434RemU43
