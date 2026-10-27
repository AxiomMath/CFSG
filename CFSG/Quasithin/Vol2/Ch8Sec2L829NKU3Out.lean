module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefsOut
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5U3T
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13.L829NK.U3Out

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {p : ℕ} {K : Type} [Field K]

abbrev M3 (K : Type) [Field K] : Type := Matrix (Fin 3) (Fin 3) K

@[expose] def mkGL (M N : M3 K) (h1 : M * N = 1) (h2 : N * M = 1) : GL (Fin 3) K := ⟨M, N, h1, h2⟩

@[expose] def dg (x y z : K) : M3 K := Matrix.diagonal ![x, y, z]

@[expose] def wM : M3 K := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

@[expose] def z0M : M3 K := !![-1, 0, 0; 0, 1, 0; 0, 0, -1]

@[expose] def uM : M3 K := !![0, 1, 0; 1, 0, 0; 0, 0, -1]

abbrev mat (g : GL (Fin 3) K) : M3 K := (g : Matrix (Fin 3) (Fin 3) K)

theorem dg_mul_dg_inv (x y z x' y' z' : K) (h1 : x * x' = 1) (h2 : y * y' = 1) (h3 : z * z' = 1) :
    dg x y z * dg x' y' z' = 1 := by
  unfold dg
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, Matrix.diagonal]

theorem mem_of_mat (h : UnitaryFieldData p 1 K) (M N : M3 K) (h1 : M * N = 1) (h2 : N * M = 1)
    (hdet : M.det = 1) (hu : (M.map h.bar)ᵀ * M = 1) :
    mkGL M N h1 h2 ∈ unitarySU p 1 K 3 :=
  (mem_unitarySU_iff h).2 ⟨hdet, hu⟩

@[expose] def mkSU (h : UnitaryFieldData p 1 K) (M N : M3 K) (h1 : M * N = 1) (h2 : N * M = 1)
    (hdet : M.det = 1) (hu : (M.map h.bar)ᵀ * M = 1) : unitarySU p 1 K 3 :=
  ⟨mkGL M N h1 h2, mem_of_mat h M N h1 h2 hdet hu⟩

@[expose] noncomputable def barEquiv (h : UnitaryFieldData p 1 K) : K ≃+* K :=
  RingEquiv.ofBijective h.bar
    (by
      haveI := h.finite
      exact ⟨(h.bar : K →+* K).injective, Finite.injective_iff_surjective.mp
        (h.bar : K →+* K).injective⟩)

theorem barEquiv_apply (h : UnitaryFieldData p 1 K) (c : K) : barEquiv h c = h.bar c := rfl

theorem ringAut_eq_refl_or_bar (h : UnitaryFieldData p 1 K) (σ : K ≃+* K) :
    σ = RingEquiv.refl K ∨ σ = barEquiv h := by
  haveI := h.finite
  have hcard : Nat.card K = p ^ 2 := by rw [h.card]
  have hp : p.Prime := h.prime
  obtain ⟨h2, -⟩ := card_ringAut_and_isCyclic hp K hcard
  have hc : Nat.card (RingAut K) = 2 := h2
  obtain ⟨y0, hy0, huniq⟩ := (Nat.card_eq_two_iff' (RingEquiv.refl K)).mp hc
  have hbar_ne : barEquiv h ≠ RingEquiv.refl K := by
    obtain ⟨c, hc'⟩ := h.exists_bar_ne
    intro heq
    apply hc'
    have := congrArg (fun e : K ≃+* K => e c) heq
    simpa [barEquiv_apply] using this
  have hyb : barEquiv h = y0 := huniq _ hbar_ne
  by_cases hσ : σ = RingEquiv.refl K
  · exact Or.inl hσ
  · right
    rw [huniq σ hσ, hyb]

theorem exists_good_a (h : UnitaryFieldData p 1 K) (hp : 13 ≤ p) :
    ∃ a : K, h.bar a * a = 1 ∧ a ^ 3 ≠ 1 ∧ a ^ 6 ≠ 1 := by
  haveI := h.finite
  have hp' : p.Prime := h.prime
  have hcardK : Nat.card K = p ^ 2 := by rw [h.card]
  have hcardU : Nat.card Kˣ = p ^ 2 - 1 := by rw [Nat.card_units, hcardK]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have key : (q + 1) ^ 2 = q * (q + 2) + 1 := by ring
  rw [hcardU, key, Nat.add_sub_cancel] at hg
  have hq0 : 0 < q := by omega
  refine ⟨((g ^ q : Kˣ) : K), ?_, ?_, ?_⟩
  · rw [h.bar_apply, pow_one, ← pow_succ, ← Units.val_pow_eq_pow_val, ← pow_mul]
    have : q * (q + 1 + 1) = q * (q + 2) := by ring
    rw [show q * (q + 1 + 1) = q * (q + 2) from this, ← hg, pow_orderOf_eq_one, Units.val_one]
  · intro h3
    have h3' : (g ^ q) ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h3)
    rw [← pow_mul] at h3'
    have hd := orderOf_dvd_of_pow_eq_one h3'
    rw [hg] at hd
    have h3d : q + 2 ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hq0 hd
    have := Nat.le_of_dvd (by norm_num) h3d
    omega
  · intro h6
    have h6' : (g ^ q) ^ 6 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h6)
    rw [← pow_mul] at h6'
    have hd := orderOf_dvd_of_pow_eq_one h6'
    rw [hg] at hd
    have h6d : q + 2 ∣ 6 := Nat.dvd_of_mul_dvd_mul_left hq0 hd
    have := Nat.le_of_dvd (by norm_num) h6d
    omega

theorem mat_eq_smul_of_inv_mul {u g : GL (Fin 3) K} {c : Kˣ}
    (hc : u⁻¹ * g = GeneralLinearGroup.scalar (Fin 3) c) :
    mat g = (c : K) • mat u := by
  have hg : g = u * GeneralLinearGroup.scalar (Fin 3) c := by
    rw [← hc, mul_inv_cancel_left]
  rw [hg]
  ext i j
  simp [mat, Matrix.mul_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply, mul_comm]

theorem rel_of_fix {f : ℕ} {h : UnitaryFieldData p f K} (A : unitaryIsom3 h) (σ : K ≃+* K)
    (g : unitarySU p f K 3)
    (hfix : psuConj h A (psuField h σ (unitaryProj h 3 g)) = unitaryProj h 3 g) :
    ∃ c : K, c ^ 3 = 1 ∧ mat (A : GL (Fin 3) K) * (mat (g : GL (Fin 3) K)).map σ =
      c • (mat (g : GL (Fin 3) K) * mat (A : GL (Fin 3) K)) := by
  change psuConj h A (psuField h σ (g : unitaryPSU h 3)) = (g : unitaryPSU h 3) at hfix
  rw [psuField_mk, psuConj_mk, QuotientGroup.eq] at hfix
  obtain ⟨c, -, hc3, hcg⟩ := mem_unitaryScalars.mp hfix
  have hcg' : ((suConj h A (suField h σ g) : unitarySU p f K 3) : GL (Fin 3) K)⁻¹ *
      (g : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hcg
  have hmat := mat_eq_smul_of_inv_mul hcg'
  rw [coe_suConj, coe_suField] at hmat
  simp only [mat, Units.val_mul, coe_glAut] at hmat
  have hc3K : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hAi : (((A⁻¹ : unitaryIsom3 h) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (A : GL (Fin 3) K).1 = 1 := by
    rw [Subgroup.coe_inv]
    exact Units.inv_mul (A : GL (Fin 3) K)
  refine ⟨(c : K)⁻¹, by rw [inv_pow, hc3K, inv_one], ?_⟩
  have key : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : GL (Fin 3) K).1 =
      (c : K) • ((A : GL (Fin 3) K).1 * (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).map σ) := by
    conv_lhs => rw [hmat]
    rw [smul_mul_assoc, Matrix.mul_assoc _ (((A⁻¹ : unitaryIsom3 h) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) _, hAi, Matrix.mul_one]
  change (A : GL (Fin 3) K).1 * (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).map σ =
    (c : K)⁻¹ • (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : GL (Fin 3) K).1)
  rw [key, smul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem nz_V1 {a b c : K} (hab : a * b = 1) (hc : c ^ 3 = 1) (h6 : a ^ 6 ≠ 1) : b - c * a ≠ 0 := by
  intro h0
  apply h6
  have h1 : c * a ^ 2 = 1 := by linear_combination (-a) * h0 + hab
  linear_combination (-(a ^ 6)) * hc + ((c * a ^ 2) ^ 2 + c * a ^ 2 + 1) * h1

theorem nz_V2 {a c : K} (hc : c ^ 3 = 1) (h3 : a ^ 3 ≠ 1) : 1 - c * a ≠ 0 := by
  intro h0
  apply h3
  linear_combination (-(a ^ 3)) * hc - ((c * a) ^ 2 + c * a + 1) * h0

theorem nz_V4 {a b c : K} (hab : a * b = 1) (hc : c ^ 3 = 1) (h6 : a ^ 6 ≠ 1) :
    a - c * b ≠ 0 := by
  intro h0
  apply h6
  have h2 : a ^ 2 = c := by linear_combination a * h0 + c * hab
  linear_combination ((a ^ 2) ^ 2 + a ^ 2 * c + c ^ 2) * h2 + hc

theorem nz_V5 {a c : K} (hc : c ^ 3 = 1) (h3 : a ^ 3 ≠ 1) : a - c ≠ 0 := by
  intro h0
  apply h3
  linear_combination (a ^ 2 + a * c + c ^ 2) * h0 + hc

theorem nz_V6 {a b c : K} (hab : a * b = 1) (hc : c ^ 3 = 1) (h3 : a ^ 3 ≠ 1) :
    1 - c * b ≠ 0 := by
  intro h0
  apply h3
  have h2 : a - c = 0 := by linear_combination a * h0 + c * hab
  linear_combination (a ^ 2 + a * c + c ^ 2) * h2 + hc

theorem nz_V7 {a b c : K} (hab : a * b = 1) (hc : c ^ 3 = 1) (h3 : a ^ 3 ≠ 1) : b - c ≠ 0 := by
  intro h0
  apply nz_V2 hc h3
  linear_combination a * h0 - hab

theorem entry_of_diag (A : M3 K) (d : Fin 3 → K) (c : K) (τ : K ≃+* K)
    (hrel : A * (Matrix.diagonal d).map τ = c • (Matrix.diagonal d * A)) (i j : Fin 3) :
    A i j * τ (d j) = c * d i * A i j := by
  rw [Matrix.diagonal_map (map_zero τ)] at hrel
  have := congrFun (congrFun hrel i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] at this
  linear_combination this

theorem psuConj_eq_conj_of_mat {h : UnitaryFieldData p 1 K} (A : unitaryIsom3 h)
    (z : unitarySU p 1 K 3) (s : Kˣ)
    (hA : mat (A : GL (Fin 3) K) = (s : K) • mat (z : GL (Fin 3) K)) :
    psuConj h A = MulAut.conj (unitaryProj h 3 z) := by
  have hAz : (A : GL (Fin 3) K) = (z : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) s := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar]
    ext i j
    have := congrFun (congrFun hA i) j
    simp only [mat, Matrix.smul_apply, smul_eq_mul] at this
    simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at this ⊢
    rw [this]
    ring
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [psuConj_mk, MulAut.conj_apply]
    have key : suConj h A g = z * g * z⁻¹ := by
      apply Subtype.ext
      simp only [coe_suConj, Subgroup.coe_mul, Subgroup.coe_inv, hAz]
      have hSg : GeneralLinearGroup.scalar (Fin 3) s * (g : GL (Fin 3) K) =
          (g : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) s :=
        (commute_scalar s (g : GL (Fin 3) K)).eq.symm
      calc (z : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) s * (g : GL (Fin 3) K) *
            ((z : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) s)⁻¹
          = (z : GL (Fin 3) K) * (GeneralLinearGroup.scalar (Fin 3) s * (g : GL (Fin 3) K)) *
            (GeneralLinearGroup.scalar (Fin 3) s)⁻¹ * (z : GL (Fin 3) K)⁻¹ := by group
        _ = (z : GL (Fin 3) K) * ((g : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) s) *
            (GeneralLinearGroup.scalar (Fin 3) s)⁻¹ * (z : GL (Fin 3) K)⁻¹ := by rw [hSg]
        _ = (z : GL (Fin 3) K) * (g : GL (Fin 3) K) * (z : GL (Fin 3) K)⁻¹ := by group
    rw [key]
    rfl

theorem psuField_refl {f : ℕ} (h : UnitaryFieldData p f K) : psuField h (RingEquiv.refl K) = 1 :=
  map_one (psuField h)

theorem wM_unit (h : UnitaryFieldData p 1 K) : (wM.map h.bar)ᵀ * wM = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [wM, Matrix.mul_apply, Fin.sum_univ_three]

theorem wM_det : (wM : M3 K).det = 1 := by
  simp [wM, Matrix.det_fin_three]

theorem wM_sq : wM * wM = (1 : M3 K) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [wM, Matrix.mul_apply, Fin.sum_univ_three]

theorem uM_unit (h : UnitaryFieldData p 1 K) : (uM.map h.bar)ᵀ * uM = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [uM, Matrix.mul_apply, Fin.sum_univ_three]

theorem uM_det : (uM : M3 K).det = 1 := by
  simp [uM, Matrix.det_fin_three]

theorem uM_sq : uM * uM = (1 : M3 K) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [uM, Matrix.mul_apply, Fin.sum_univ_three]

theorem z0M_unit (h : UnitaryFieldData p 1 K) : (z0M.map h.bar)ᵀ * z0M = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [z0M, Matrix.mul_apply, Fin.sum_univ_three]

theorem z0M_det : (z0M : M3 K).det = 1 := by
  simp [z0M, Matrix.det_fin_three]

theorem z0M_sq : z0M * z0M = (1 : M3 K) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [z0M, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] noncomputable def wSU (h : UnitaryFieldData p 1 K) : unitarySU p 1 K 3 :=
  mkSU h wM wM wM_sq wM_sq wM_det (wM_unit h)

@[expose] noncomputable def z0SU (h : UnitaryFieldData p 1 K) : unitarySU p 1 K 3 :=
  mkSU h z0M z0M z0M_sq z0M_sq z0M_det (z0M_unit h)

@[expose] noncomputable def uSU (h : UnitaryFieldData p 1 K) : unitarySU p 1 K 3 :=
  mkSU h uM uM uM_sq uM_sq uM_det (uM_unit h)

theorem wSU_mat (h : UnitaryFieldData p 1 K) : mat (wSU h : GL (Fin 3) K) = wM := rfl
theorem z0SU_mat (h : UnitaryFieldData p 1 K) : mat (z0SU h : GL (Fin 3) K) = z0M := rfl
theorem uSU_mat (h : UnitaryFieldData p 1 K) : mat (uSU h : GL (Fin 3) K) = uM := rfl

theorem wM00 : wM 0 0 = (0 : K) := by simp [wM]
theorem wM01 : wM 0 1 = (0 : K) := by simp [wM]
theorem wM02 : wM 0 2 = (1 : K) := by simp [wM]
theorem wM10 : wM 1 0 = (0 : K) := by simp [wM]
theorem wM11 : wM 1 1 = (-1 : K) := by simp [wM]
theorem wM12 : wM 1 2 = (0 : K) := by simp [wM]
theorem wM20 : wM 2 0 = (1 : K) := by simp [wM]
theorem wM21 : wM 2 1 = (0 : K) := by simp [wM]
theorem wM22 : wM 2 2 = (0 : K) := by simp [wM]
theorem uM00 : uM 0 0 = (0 : K) := by simp [uM]
theorem uM01 : uM 0 1 = (1 : K) := by simp [uM]
theorem uM02 : uM 0 2 = (0 : K) := by simp [uM]
theorem uM10 : uM 1 0 = (1 : K) := by simp [uM]
theorem uM11 : uM 1 1 = (0 : K) := by simp [uM]
theorem uM12 : uM 1 2 = (0 : K) := by simp [uM]
theorem uM20 : uM 2 0 = (0 : K) := by simp [uM]
theorem uM21 : uM 2 1 = (0 : K) := by simp [uM]
theorem uM22 : uM 2 2 = (-1 : K) := by simp [uM]

theorem bar_case_false (h : UnitaryFieldData p 1 K) {a : K} (ha0 : a ≠ 0) (hbar : h.bar a = a⁻¹)
    (ha3 : a ^ 3 ≠ 1) (ha6 : a ^ 6 ≠ 1) (A : unitaryIsom3 h)
    (t₁ t₂ : unitarySU p 1 K 3) (ht₁ : mat (t₁ : GL (Fin 3) K) = dg a a⁻¹ 1)
    (ht₂ : mat (t₂ : GL (Fin 3) K) = dg 1 a a⁻¹)
    (hf1 : psuConj h A (psuField h (barEquiv h) (unitaryProj h 3 t₁)) = unitaryProj h 3 t₁)
    (hf2 : psuConj h A (psuField h (barEquiv h) (unitaryProj h 3 t₂)) = unitaryProj h 3 t₂) :
    False := by
  have hab : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
  obtain ⟨c₁, hc₁, r₁⟩ := rel_of_fix A (barEquiv h) t₁ hf1
  obtain ⟨c₂, hc₂, r₂⟩ := rel_of_fix A (barEquiv h) t₂ hf2
  rw [ht₁] at r₁
  rw [ht₂] at r₂
  have hτa : barEquiv h a = a⁻¹ := by rw [barEquiv_apply, hbar]
  have hτb : barEquiv h a⁻¹ = a := by rw [barEquiv_apply, map_inv₀, hbar, inv_inv]
  have e00 := entry_of_diag (mat (A : GL (Fin 3) K)) ![a, a⁻¹, 1] c₁ (barEquiv h) r₁ 0 0
  have e02 := entry_of_diag (mat (A : GL (Fin 3) K)) ![a, a⁻¹, 1] c₁ (barEquiv h) r₁ 0 2
  have e01 := entry_of_diag (mat (A : GL (Fin 3) K)) ![1, a, a⁻¹] c₂ (barEquiv h) r₂ 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hτa, hτb,
    Matrix.cons_val_two, Matrix.tail_cons, map_one] at e00 e02 e01
  have z00 : mat (A : GL (Fin 3) K) 0 0 = 0 :=
    (mul_eq_zero.mp (show mat (A : GL (Fin 3) K) 0 0 * (a⁻¹ - c₁ * a) = 0 by
      linear_combination e00)).resolve_right (nz_V1 hab hc₁ ha6)
  have z02 : mat (A : GL (Fin 3) K) 0 2 = 0 :=
    (mul_eq_zero.mp (show mat (A : GL (Fin 3) K) 0 2 * (1 - c₁ * a) = 0 by
      linear_combination e02)).resolve_right (nz_V2 hc₁ ha3)
  have z01 : mat (A : GL (Fin 3) K) 0 1 = 0 :=
    (mul_eq_zero.mp (show mat (A : GL (Fin 3) K) 0 1 * (a⁻¹ - c₂) = 0 by
      linear_combination e01)).resolve_right (nz_V7 hab hc₂ ha3)
  have hI : mat (A : GL (Fin 3) K) * mat ((A : GL (Fin 3) K)⁻¹) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have := congrFun (congrFun hI 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, z00, z01, z02] at this

theorem refl_case (h : UnitaryFieldData p 1 K) {a : K} (ha0 : a ≠ 0)
    (ha3 : a ^ 3 ≠ 1) (ha6 : a ^ 6 ≠ 1) (A : unitaryIsom3 h)
    (t₁ w : unitarySU p 1 K 3) (ht₁ : mat (t₁ : GL (Fin 3) K) = dg a a⁻¹ 1)
    (hw : mat (w : GL (Fin 3) K) = wM)
    (hf1 : psuConj h A (unitaryProj h 3 t₁) = unitaryProj h 3 t₁)
    (hf3 : psuConj h A (unitaryProj h 3 w) = unitaryProj h 3 w)
    (hinv : psuConj h (A * A) = 1) :
    ∃ x : unitaryPSU h 3, psuConj h A = MulAut.conj x := by
  have hab : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
  have hf1' : psuConj h A (psuField h (RingEquiv.refl K) (unitaryProj h 3 t₁)) =
      unitaryProj h 3 t₁ := by rw [psuField_refl, MulAut.one_apply]; exact hf1
  have hf3' : psuConj h A (psuField h (RingEquiv.refl K) (unitaryProj h 3 w)) =
      unitaryProj h 3 w := by rw [psuField_refl, MulAut.one_apply]; exact hf3
  obtain ⟨c₁, hc₁, r₁⟩ := rel_of_fix A (RingEquiv.refl K) t₁ hf1'
  obtain ⟨c₂, hc₂, r₂⟩ := rel_of_fix A (RingEquiv.refl K) w hf3'
  rw [ht₁] at r₁
  rw [hw] at r₂
  have hfu : psuConj h (A * A) (psuField h (RingEquiv.refl K) (unitaryProj h 3 (uSU h))) =
      unitaryProj h 3 (uSU h) := by
    rw [psuField_refl, MulAut.one_apply, hinv, MulAut.one_apply]
  obtain ⟨c₃, hc₃, r₃⟩ := rel_of_fix (A * A) (RingEquiv.refl K) (uSU h) hfu
  rw [uSU_mat] at r₃
  have hAA : mat ((A * A : unitaryIsom3 h) : GL (Fin 3) K) =
      mat (A : GL (Fin 3) K) * mat (A : GL (Fin 3) K) := rfl
  rw [hAA] at r₃
  set M := mat (A : GL (Fin 3) K) with hM
  have E : ∀ i j, M i j * (![a, a⁻¹, 1] j) = c₁ * (![a, a⁻¹, 1] i) * M i j := by
    intro i j
    have := entry_of_diag M ![a, a⁻¹, 1] c₁ (RingEquiv.refl K) r₁ i j
    simpa using this
  have z01 : M 0 1 = 0 := by
    have e := E 0 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e
    exact (mul_eq_zero.mp (show M 0 1 * (a⁻¹ - c₁ * a) = 0 by linear_combination e)).resolve_right
      (nz_V1 hab hc₁ ha6)
  have z10 : M 1 0 = 0 := by
    have e := E 1 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e
    exact (mul_eq_zero.mp (show M 1 0 * (a - c₁ * a⁻¹) = 0 by linear_combination e)).resolve_right
      (nz_V4 hab hc₁ ha6)
  have z02 : M 0 2 = 0 := by
    have e := E 0 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at e
    exact (mul_eq_zero.mp (show M 0 2 * (1 - c₁ * a) = 0 by linear_combination e)).resolve_right
      (nz_V2 hc₁ ha3)
  have z20 : M 2 0 = 0 := by
    have e := E 2 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at e
    exact (mul_eq_zero.mp (show M 2 0 * (a - c₁) = 0 by linear_combination e)).resolve_right
      (nz_V5 hc₁ ha3)
  have z12 : M 1 2 = 0 := by
    have e := E 1 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at e
    exact (mul_eq_zero.mp (show M 1 2 * (1 - c₁ * a⁻¹) = 0 by linear_combination e)).resolve_right
      (nz_V6 hab hc₁ ha3)
  have z21 : M 2 1 = 0 := by
    have e := E 2 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at e
    exact (mul_eq_zero.mp (show M 2 1 * (a⁻¹ - c₁) = 0 by linear_combination e)).resolve_right
      (nz_V7 hab hc₁ ha3)
  have hMI : M * mat ((A : GL (Fin 3) K)⁻¹) = 1 := by
    rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have d00 : M 0 0 ≠ 0 := by
    intro h0
    have := congrFun (congrFun hMI 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, h0, z01, z02] at this
  have d22 : M 2 2 ≠ 0 := by
    intro h0
    have := congrFun (congrFun hMI 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, h0, z20, z21] at this
  have w02 : M 0 0 = c₂ * M 2 2 := by
    have e := congrFun (congrFun r₂ 0) 2
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul,
      Matrix.map_apply, RingEquiv.refl_apply, wM00, wM01, wM02, wM10, wM11, wM12, wM20, wM21,
      wM22, z01, z02, z10, z12, z20, z21] at e
    linear_combination e
  have w20 : M 2 2 = c₂ * M 0 0 := by
    have e := congrFun (congrFun r₂ 2) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul,
      Matrix.map_apply, RingEquiv.refl_apply, wM00, wM01, wM02, wM10, wM11, wM12, wM20, wM21,
      wM22, z01, z02, z10, z12, z20, z21] at e
    linear_combination e
  have hsq0 : (1 - c₂ ^ 2) * M 0 0 = 0 := by linear_combination w02 + c₂ * w20
  have hsq : c₂ ^ 2 = 1 := by
    have := (mul_eq_zero.mp hsq0).resolve_right d00
    linear_combination -this
  have hc2 : c₂ = 1 := by linear_combination hc₂ - c₂ * hsq
  have h22 : M 2 2 = M 0 0 := by
    rw [hc2, one_mul] at w20
    exact w20
  have e33 := congrFun (congrFun r₃ 2) 2
  have e01 := congrFun (congrFun r₃ 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul,
    Matrix.map_apply, RingEquiv.refl_apply, uM00, uM01, uM02, uM10, uM11, uM12, uM20, uM21,
    uM22, z01, z02, z10, z12, z20, z21] at e33 e01
  have hc3 : c₃ = 1 := by
    have h1 : (M 2 2 * M 2 2) * (1 - c₃) = 0 := by linear_combination -e33
    have := (mul_eq_zero.mp h1).resolve_left (mul_ne_zero d22 d22)
    linear_combination -this
  subst hc3
  have hsq11 : (M 1 1 - M 0 0) * (M 1 1 + M 0 0) = 0 := by linear_combination -e01
  rcases mul_eq_zero.mp hsq11 with h1 | h1
  ·
    have hM11 : M 1 1 = M 0 0 := by linear_combination h1
    refine ⟨unitaryProj h 3 1, ?_⟩
    apply psuConj_eq_conj_of_mat A 1 (Units.mk0 (M 0 0) d00)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [← hM, z01, z02, z10, z12, z20, z21, hM11, h22, Units.val_mk0]
  ·
    have hM11 : M 1 1 = -M 0 0 := by linear_combination h1
    refine ⟨unitaryProj h 3 (z0SU h), ?_⟩
    apply psuConj_eq_conj_of_mat A (z0SU h) (Units.mk0 (-M 0 0) (neg_ne_zero.mpr d00))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [← hM, z01, z02, z10, z12, z20, z21, hM11, h22, Units.val_mk0, z0SU_mat, z0M]

theorem core_u3 (h : UnitaryFieldData p 1 K) (hq : 2 < p ^ 1) {a : K} (ha : h.bar a * a = 1)
    (ha3 : a ^ 3 ≠ 1) (ha6 : a ^ 6 ≠ 1)
    (t₁ t₂ w : unitarySU p 1 K 3) (ht₁ : mat (t₁ : GL (Fin 3) K) = dg a a⁻¹ 1)
    (ht₂ : mat (t₂ : GL (Fin 3) K) = dg 1 a a⁻¹) (hw : mat (w : GL (Fin 3) K) = wM)
    (y : MulAut (unitaryPSU h 3)) (hy : y * y = 1)
    (h1 : y (unitaryProj h 3 t₁) = unitaryProj h 3 t₁)
    (h2 : y (unitaryProj h 3 t₂) = unitaryProj h 3 t₂)
    (h3 : y (unitaryProj h 3 w) = unitaryProj h 3 w) :
    ∃ x : unitaryPSU h 3, y = MulAut.conj x := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hbar : h.bar a = a⁻¹ := eq_inv_of_mul_eq_one_left ha
  obtain ⟨A, σ, hyA⟩ := exists_psuConj_mul_psuField (h := h) hq y
  rcases ringAut_eq_refl_or_bar h σ with rfl | rfl
  · have hy' : y = psuConj h A := by rw [hyA, psuField_refl, mul_one]
    have hinv : psuConj h (A * A) = 1 := by rw [map_mul, ← hy', hy]
    rw [hy'] at h1 h3
    obtain ⟨x, hx⟩ := refl_case h ha0 ha3 ha6 A t₁ w ht₁ hw h1 h3 hinv
    exact ⟨x, by rw [hy', hx]⟩
  · exfalso
    rw [hyA, MulAut.mul_apply] at h1 h2
    exact bar_case_false h ha0 hbar ha3 ha6 A t₁ t₂ ht₁ ht₂ h1 h2

theorem dihedral_conj {G : Type} [Group G] {a b : G} (hb : b ^ 2 = 1) (hba : b * a * b = a⁻¹)
    (k : ℤ) : b * a ^ k * b = a ^ (-k) := by
  have hb' : b⁻¹ = b := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hb]
  have h1 : MulAut.conj b a = a⁻¹ := by
    rw [MulAut.conj_apply, hb', hba]
  have h2 := map_zpow (MulAut.conj b) a k
  rw [h1, _root_.inv_zpow', MulAut.conj_apply, hb'] at h2
  exact h2

theorem dihedral_swap {G : Type} [Group G] {a b : G} (hb : b ^ 2 = 1) (hba : b * a * b = a⁻¹)
    (k : ℤ) : b * a ^ k = a ^ (-k) * b := by
  have h := dihedral_conj hb hba k
  calc b * a ^ k = (b * a ^ k * b) * b := by rw [mul_assoc, ← sq, hb, mul_one]
    _ = a ^ (-k) * b := by rw [h]

theorem dihedral_closure_pow {G : Type} [Group G] {a b : G} (hb : b ^ 2 = 1)
    (hba : b * a * b = a⁻¹) : ∀ x ∈ Subgroup.closure ({a, b} : Set G),
      ∃ (i : ℤ) (j : ℕ), j < 2 ∧ x = a ^ i * b ^ j := by
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq, hb])
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by norm_num, by simp⟩
    · exact ⟨0, 1, by norm_num, by simp⟩
  | one => exact ⟨0, 0, by norm_num, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, hj, rfl⟩ := hx
    obtain ⟨k, l, hl, rfl⟩ := hy
    interval_cases j <;> interval_cases l
    · exact ⟨i + k, 0, by norm_num, by simp [_root_.zpow_add]⟩
    · exact ⟨i + k, 1, by norm_num, by simp [_root_.zpow_add, mul_assoc]⟩
    · refine ⟨i + -k, 1, by norm_num, ?_⟩
      calc a ^ i * b ^ 1 * (a ^ k * b ^ 0) = a ^ i * (b * a ^ k) := by simp [mul_assoc]
        _ = a ^ i * (a ^ (-k) * b) := by rw [dihedral_swap hb hba k]
        _ = a ^ (i + -k) * b ^ 1 := by simp [mul_assoc, _root_.zpow_add]
    · refine ⟨i + -k, 0, by norm_num, ?_⟩
      calc a ^ i * b ^ 1 * (a ^ k * b ^ 1) = a ^ i * (b * a ^ k * b) := by simp [mul_assoc]
        _ = a ^ i * a ^ (-k) := by rw [dihedral_conj hb hba k]
        _ = a ^ (i + -k) * b ^ 0 := by simp [_root_.zpow_add]
  | inv x _ hx =>
    obtain ⟨i, j, hj, rfl⟩ := hx
    interval_cases j
    · exact ⟨-i, 0, by norm_num, by simp [_root_.zpow_neg]⟩
    · refine ⟨i, 1, by norm_num, ?_⟩
      calc (a ^ i * b ^ 1)⁻¹ = b⁻¹ * (a ^ i)⁻¹ := by simp [_root_.mul_inv_rev]
        _ = b * a ^ (-i) := by rw [hb', ← _root_.zpow_neg]
        _ = a ^ (-(-i)) * b := dihedral_swap hb hba (-i)
        _ = a ^ i * b ^ 1 := by simp

theorem isPGroup_two_dihedral_closure {G : Type} [Group G] {a b : G} (ha : a ^ 4 = 1)
    (hb : b ^ 2 = 1) (hba : b * a * b = a⁻¹) :
    IsPGroup 2 (Subgroup.closure ({a, b} : Set G)) := by
  intro g
  obtain ⟨i, j, hj, hg⟩ := dihedral_closure_pow hb hba g.1 g.2
  refine ⟨2, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, hg, Subgroup.coe_one]
  have h2 : (a ^ i * b ^ j) ^ (2 ^ 2) = 1 := by
    rw [show (2 : ℕ) ^ 2 = 4 from rfl]
    interval_cases j
    · simp only [pow_zero, mul_one]
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, _root_.zpow_natCast,
        ha, _root_.one_zpow]
    · have hsq : (a ^ i * b ^ 1) ^ 2 = 1 := by
        have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq, hb])
        rw [pow_one, sq, mul_assoc, ← mul_assoc b, dihedral_conj hb hba i, ← _root_.zpow_add,
          add_neg_cancel, zpow_zero]
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, one_pow]
  exact h2

@[expose] def iM : M3 K := !![0, 0, 1; 0, 1, 0; -1, 0, 0]

@[expose] def iInvM : M3 K := !![0, 0, -1; 0, 1, 0; 1, 0, 0]

theorem iM_mul_iInvM : (iM : M3 K) * iInvM = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [iM, iInvM, Matrix.mul_apply, Fin.sum_univ_three]

theorem iInvM_mul_iM : (iInvM : M3 K) * iM = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [iM, iInvM, Matrix.mul_apply, Fin.sum_univ_three]

theorem iM_det : (iM : M3 K).det = 1 := by
  simp [iM, Matrix.det_fin_three]

theorem iM_unit (h : UnitaryFieldData p 1 K) : ((iM : M3 K).map h.bar)ᵀ * iM = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [iM, Matrix.mul_apply, Fin.sum_univ_three]

theorem iM_sq : (iM : M3 K) * iM = z0M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [iM, z0M, Matrix.mul_apply, Fin.sum_univ_three]

theorem wM_iM_wM : (wM : M3 K) * iM * wM = iInvM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [wM, iM, iInvM, Matrix.mul_apply, Fin.sum_univ_three]

theorem iInvM_det : (iInvM : M3 K).det = 1 := by
  simp [iInvM, Matrix.det_fin_three]

theorem iInvM_unit (h : UnitaryFieldData p 1 K) : ((iInvM : M3 K).map h.bar)ᵀ * iInvM = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [iInvM, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] noncomputable def iSU (h : UnitaryFieldData p 1 K) : unitarySU p 1 K 3 :=
  mkSU h iM iInvM iM_mul_iInvM iInvM_mul_iM iM_det (iM_unit h)

@[expose] noncomputable def iSUinv (h : UnitaryFieldData p 1 K) : unitarySU p 1 K 3 :=
  mkSU h iInvM iM iInvM_mul_iM iM_mul_iInvM iInvM_det (iInvM_unit h)

theorem iSU_mat (h : UnitaryFieldData p 1 K) : mat (iSU h : GL (Fin 3) K) = iM := rfl

theorem iSU_sq (h : UnitaryFieldData p 1 K) : iSU h * iSU h = z0SU h := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  exact iM_sq

theorem z0SU_sq' (h : UnitaryFieldData p 1 K) : z0SU h * z0SU h = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one]
  exact z0M_sq

theorem iSU_pow_four (h : UnitaryFieldData p 1 K) : iSU h ^ 4 = 1 := by
  have h2 : iSU h ^ 2 = z0SU h := by rw [sq]; exact iSU_sq h
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, sq, z0SU_sq']

theorem iSU_inv_eq (h : UnitaryFieldData p 1 K) : (iSU h)⁻¹ = iSUinv h := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one]
  exact iM_mul_iInvM

theorem wSU_iSU_wSU (h : UnitaryFieldData p 1 K) :
    wSU h * iSU h * wSU h = iSUinv h := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  exact wM_iM_wM

theorem wSU_sq' (h : UnitaryFieldData p 1 K) : wSU h * wSU h = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one]
  exact wM_sq

theorem scalar_eq_one_iff (d : Kˣ) :
    (GeneralLinearGroup.scalar (Fin 3) d : GL (Fin 3) K) = 1 ↔ d = 1 := by
  constructor
  · intro hd
    have h0 : ((GeneralLinearGroup.scalar (Fin 3) d : GL (Fin 3) K) : M3 K) 0 0 = (d : K) := by
      simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    rw [hd] at h0
    apply Units.ext
    simpa using h0.symm
  · rintro rfl
    simp

theorem commute_of_proj_commute (h : UnitaryFieldData p 1 K) {n : ℕ} (hn : Nat.Coprime n 3)
    {g m : unitarySU p 1 K 3} (hgn : g ^ n = 1)
    (hc : unitaryProj h 3 m * unitaryProj h 3 g = unitaryProj h 3 g * unitaryProj h 3 m) :
    m * g = g * m := by
  have h1 : unitaryProj h 3 (m * g) = unitaryProj h 3 (g * m) := by
    rw [map_mul, map_mul]
    exact hc
  have hX := QuotientGroup.eq.mp h1
  obtain ⟨c, -, hc3, hcg⟩ := mem_unitaryScalars.mp hX
  have hcomm : Commute g ((m * g)⁻¹ * (g * m)) :=
    (Subgroup.mem_center_iff.mp (unitaryScalars_le_center h 3 hX)) g
  have hXn : ((m * g)⁻¹ * (g * m)) ^ n = 1 := by
    have e : g * ((m * g)⁻¹ * (g * m)) = m⁻¹ * g * m := by group
    have hconj : (m⁻¹ * g * m) ^ n = 1 := by
      rw [show m⁻¹ * g * m = m⁻¹ * g * m⁻¹⁻¹ by group, conj_pow, hgn]
      group
    rw [← e] at hconj
    rw [hcomm.mul_pow, hgn, one_mul] at hconj
    exact hconj
  have hcn : c ^ n = 1 := by
    have h2 := congrArg (fun x : unitarySU p 1 K 3 => (x : GL (Fin 3) K)) hXn
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hcg, ← map_pow, scalar_eq_one_iff] at h2
    exact h2
  have hc1 : c = 1 := by
    have hg : c ^ Nat.gcd n 3 = 1 := pow_gcd_eq_one.mpr ⟨hcn, hc3⟩
    rw [Nat.Coprime.gcd_eq_one hn, pow_one] at hg
    exact hg
  have hX1 : (m * g)⁻¹ * (g * m) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_one, hcg, hc1]
    exact (scalar_eq_one_iff 1).mpr rfl
  exact inv_mul_eq_one.mp hX1

theorem iM00 : iM 0 0 = (0 : K) := by simp [iM]
theorem iM01 : iM 0 1 = (0 : K) := by simp [iM]
theorem iM02 : iM 0 2 = (1 : K) := by simp [iM]
theorem iM10 : iM 1 0 = (0 : K) := by simp [iM]
theorem iM11 : iM 1 1 = (1 : K) := by simp [iM]
theorem iM12 : iM 1 2 = (0 : K) := by simp [iM]
theorem iM20 : iM 2 0 = (-1 : K) := by simp [iM]
theorem iM21 : iM 2 1 = (0 : K) := by simp [iM]
theorem iM22 : iM 2 2 = (0 : K) := by simp [iM]

theorem two_ne_zero_of_prime (h : UnitaryFieldData p 1 K) (hp : p.Prime) (hp4 : p % 4 = 1) :
    (2 : K) ≠ 0 := by
  intro h0
  haveI := h.charP
  have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp h2
  have hle := Nat.le_of_dvd (by norm_num) hd
  have := hp.two_le
  omega

theorem diag_of_commute {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (X : M3 K)
    (hI : X * iM = iM * X) (hW : X * wM = wM * X) :
    X = dg (X 0 0) (X 1 1) (X 0 0) := by
  have e00 := congrFun (congrFun hI 0) 0
  have e02 := congrFun (congrFun hI 0) 2
  have e01 := congrFun (congrFun hI 0) 1
  have e21 := congrFun (congrFun hI 2) 1
  have e10 := congrFun (congrFun hI 1) 0
  have e12 := congrFun (congrFun hI 1) 2
  have f00 := congrFun (congrFun hW 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three, iM00, iM01, iM02, iM10, iM11, iM12, iM20,
    iM21, iM22, wM00, wM01, wM02, wM10, wM11, wM12, wM20, wM21, wM22, mul_zero, zero_mul,
    mul_one, one_mul, add_zero, zero_add] at e00 e02 e01 e21 e10 e12 f00
  have z01 : X 0 1 = 0 := by
    have : (2 : K) * X 0 1 = 0 := by linear_combination e01 + e21
    exact (mul_eq_zero.mp this).resolve_left h2
  have z21 : X 2 1 = 0 := by linear_combination z01 - e01
  have z10 : X 1 0 = 0 := by
    have : (2 : K) * X 1 0 = 0 := by linear_combination e12 - e10
    exact (mul_eq_zero.mp this).resolve_left h2
  have z12 : X 1 2 = 0 := by linear_combination z10 - e12
  have z02 : X 0 2 = 0 := by
    have : (2 : K) * X 0 2 = 0 := by linear_combination f00 - e00
    exact (mul_eq_zero.mp this).resolve_left h2
  have z20 : X 2 0 = 0 := by linear_combination z02 - f00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, z01, z02, z10, z12, z20, z21, Matrix.diagonal_apply]
  · linear_combination -e02

theorem dg_pow (x y z : K) (N : ℕ) : (dg x y z) ^ N = dg (x ^ N) (y ^ N) (z ^ N) := by
  unfold dg
  rw [Matrix.diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> simp

theorem gcd_two_pow_dvd (k p : ℕ) (hp4 : p % 4 = 1) : Nat.gcd (2 ^ k) (p + 1) ∣ 2 := by
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Nat.gcd_dvd_left (2 ^ k) (p + 1))
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · rw [hjeq]
    interval_cases j <;> simp
  · exfalso
    have h4 : 2 ^ 2 ∣ Nat.gcd (2 ^ k) (p + 1) := by
      rw [hjeq]
      exact pow_dvd_pow 2 hj2
    have h4' : 4 ∣ p + 1 := (show (4 : ℕ) = 2 ^ 2 from rfl) ▸ h4.trans (Nat.gcd_dvd_right _ _)
    omega

theorem center_sub_z0 (h : UnitaryFieldData p 1 K) (hp : p.Prime) (hp4 : p % 4 = 1)
    {S : Subgroup (unitaryPSU h 3)} (hS : IsPGroup 2 S)
    (hI : unitaryProj h 3 (iSU h) ∈ S) (hW : unitaryProj h 3 (wSU h) ∈ S)
    {m : unitaryPSU h 3} (hmS : m ∈ S) (hmc : ∀ s ∈ S, s * m = m * s) :
    m = 1 ∨ m = unitaryProj h 3 (z0SU h) := by
  have hsI : unitaryProj h 3 (iSU h) * m = m * unitaryProj h 3 (iSU h) := hmc _ hI
  have hsW : unitaryProj h 3 (wSU h) * m = m * unitaryProj h 3 (wSU h) := hmc _ hW
  obtain ⟨mt, rfl⟩ := unitaryProj_surjective h 3 m
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_prime h hp hp4
  have cI : mt * iSU h = iSU h * mt :=
    commute_of_proj_commute h (n := 4) (by norm_num) (iSU_pow_four h) hsI.symm
  have cW : mt * wSU h = wSU h * mt :=
    commute_of_proj_commute h (n := 2) (by norm_num) (by rw [sq]; exact wSU_sq' h) hsW.symm
  have mI : ((mt : GL (Fin 3) K) : M3 K) * iM = iM * ((mt : GL (Fin 3) K) : M3 K) := by
    have := congrArg (fun g : unitarySU p 1 K 3 => ((g : GL (Fin 3) K) : M3 K)) cI
    simpa [Subgroup.coe_mul, Units.val_mul, iSU_mat] using this
  have mW : ((mt : GL (Fin 3) K) : M3 K) * wM = wM * ((mt : GL (Fin 3) K) : M3 K) := by
    have := congrArg (fun g : unitarySU p 1 K 3 => ((g : GL (Fin 3) K) : M3 K)) cW
    simpa [Subgroup.coe_mul, Units.val_mul, wSU_mat] using this
  obtain ⟨β, γ, hβγ⟩ : ∃ β γ : K, ((mt : GL (Fin 3) K) : M3 K) = dg β γ β :=
    ⟨_, _, diag_of_commute h2 _ mI mW⟩
  have hdet : β * γ * β = 1 := by
    have h0 := ((mem_unitarySU_iff h).mp mt.2).1
    rw [hβγ] at h0
    simpa [dg, Matrix.det_diagonal, Fin.prod_univ_three] using h0
  have hu : ((dg β γ β : M3 K).map h.bar)ᵀ * dg β γ β = 1 := by
    have h0 := ((mem_unitarySU_iff h).mp mt.2).2
    rw [hβγ] at h0
    exact h0
  have hu00 : h.bar β * β = 1 := by
    have := congrFun (congrFun hu 0) 0
    simpa [dg, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] using this
  have hβp : β ^ (p + 1) = 1 := by
    have h0 := hu00
    rw [h.bar_apply, pow_one] at h0
    rw [pow_succ]
    exact h0
  obtain ⟨k, hk⟩ := hS ⟨unitaryProj h 3 mt, hmS⟩
  have hk' : (unitaryProj h 3 mt) ^ 2 ^ k = 1 := by
    have := congrArg (fun x : S => (x : unitaryPSU h 3)) hk
    simpa [Subgroup.coe_pow] using this
  have hsc : mt ^ 2 ^ k ∈ unitaryScalars h 3 := by
    rw [← ker_unitaryProj]
    apply MonoidHom.mem_ker.mpr
    rw [map_pow]
    exact hk'
  obtain ⟨c, -, hc3, hcg⟩ := mem_unitaryScalars.mp hsc
  set N := 2 ^ k with hN
  have e2 : ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : M3 K) = (dg β γ β) ^ N := by
    rw [← hβγ, ← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hcg]
  rw [dg_pow] at e2
  have hβN : β ^ N = (c : K) := by
    have := congrFun (congrFun e2 0) 0
    simpa [dg, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply] using this.symm
  have hγN : γ ^ N = (c : K) := by
    have := congrFun (congrFun e2 1) 1
    simpa [dg, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply] using this.symm
  have hc3K : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hxN : (β ^ 3) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hβN, hc3K]
  have hxp : (β ^ 3) ^ (p + 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hβp, one_pow]
  have hsq : (β ^ 3) ^ 2 = 1 := by
    have hg : (β ^ 3) ^ Nat.gcd N (p + 1) = 1 := pow_gcd_eq_one.mpr ⟨hxN, hxp⟩
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_pow_eq_one hg).trans (gcd_two_pow_dvd k p hp4))
  have hcube : β ^ 3 = 1 ∨ β ^ 3 = -1 := by
    have : β ^ 3 * β ^ 3 = 1 := by rw [← sq]; exact hsq
    exact mul_self_eq_one_iff.mp this
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0] at hcube
    norm_num at hcube
  rcases hcube with hc1 | hc1
  ·
    have hγβ : γ = β := by
      have h0 : β * β * (γ - β) = 0 := by linear_combination hdet - hc1
      have := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hβ0 hβ0)
      linear_combination this
    left
    apply MonoidHom.mem_ker.mp
    rw [ker_unitaryProj]
    refine mem_unitaryScalars.mpr ⟨Units.mk0 β hβ0, ?_, ?_, ?_⟩
    · show β * h.bar β = 1
      rw [mul_comm]
      exact hu00
    · apply Units.ext
      simpa using hc1
    · apply Units.ext
      rw [GeneralLinearGroup.coe_scalar]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hβγ, dg, hγβ, Matrix.scalar_apply, Matrix.diagonal_apply]
  ·
    have hγβ : γ = -β := by
      have h0 : β * β * (γ + β) = 0 := by linear_combination hdet + hc1
      have := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hβ0 hβ0)
      linear_combination this
    right
    have hmt : (mt : GL (Fin 3) K) =
        (z0SU h : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (-β) (neg_ne_zero.mpr hβ0)) := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hβγ, dg, hγβ, z0SU_mat, z0M, Matrix.mul_apply, Fin.sum_univ_three,
          Matrix.scalar_apply, Matrix.diagonal_apply]
    have hmem : (z0SU h)⁻¹ * mt ∈ unitaryScalars h 3 := by
      refine mem_unitaryScalars.mpr ⟨Units.mk0 (-β) (neg_ne_zero.mpr hβ0), ?_, ?_, ?_⟩
      · show (-β) * h.bar (-β) = 1
        rw [map_neg]
        linear_combination hu00
      · apply Units.ext
        simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
        linear_combination -hc1
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, hmt, inv_mul_cancel_left]
    have h1 : unitaryProj h 3 ((z0SU h)⁻¹ * mt) = 1 :=
      MonoidHom.mem_ker.mp (by rw [ker_unitaryProj]; exact hmem)
    rw [map_mul, map_inv] at h1
    exact (inv_mul_eq_one.mp h1).symm

theorem tM1_det {a : K} (ha0 : a ≠ 0) : (dg a a⁻¹ 1 : M3 K).det = 1 := by
  simp [dg, Matrix.det_diagonal, Fin.prod_univ_three, ha0]

theorem tM2_det {a : K} (ha0 : a ≠ 0) : (dg 1 a a⁻¹ : M3 K).det = 1 := by
  simp [dg, Matrix.det_diagonal, Fin.prod_univ_three, ha0]

theorem tM1_unit (h : UnitaryFieldData p 1 K) {a : K} (ha0 : a ≠ 0) (hbar : h.bar a = a⁻¹) :
    ((dg a a⁻¹ 1 : M3 K).map h.bar)ᵀ * dg a a⁻¹ 1 = 1 := by
  have hba' : h.bar a⁻¹ = a := by rw [map_inv₀, hbar, inv_inv]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dg, Matrix.mul_apply, Fin.sum_univ_three, hbar, hba', ha0, Matrix.diagonal_apply]

theorem tM2_unit (h : UnitaryFieldData p 1 K) {a : K} (ha0 : a ≠ 0) (hbar : h.bar a = a⁻¹) :
    ((dg 1 a a⁻¹ : M3 K).map h.bar)ᵀ * dg 1 a a⁻¹ = 1 := by
  have hba' : h.bar a⁻¹ = a := by rw [map_inv₀, hbar, inv_inv]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dg, Matrix.mul_apply, Fin.sum_univ_three, hbar, hba', ha0, Matrix.diagonal_apply]

@[expose] noncomputable def tSU1 (h : UnitaryFieldData p 1 K) {a : K} (ha0 : a ≠ 0)
    (hbar : h.bar a = a⁻¹) : unitarySU p 1 K 3 :=
  mkSU h (dg a a⁻¹ 1) (dg a⁻¹ a 1)
    (dg_mul_dg_inv _ _ _ _ _ _ (mul_inv_cancel₀ ha0) (inv_mul_cancel₀ ha0) (mul_one 1))
    (dg_mul_dg_inv _ _ _ _ _ _ (inv_mul_cancel₀ ha0) (mul_inv_cancel₀ ha0) (mul_one 1))
    (tM1_det ha0) (tM1_unit h ha0 hbar)

@[expose] noncomputable def tSU2 (h : UnitaryFieldData p 1 K) {a : K} (ha0 : a ≠ 0)
    (hbar : h.bar a = a⁻¹) : unitarySU p 1 K 3 :=
  mkSU h (dg 1 a a⁻¹) (dg 1 a⁻¹ a)
    (dg_mul_dg_inv _ _ _ _ _ _ (mul_one 1) (mul_inv_cancel₀ ha0) (inv_mul_cancel₀ ha0))
    (dg_mul_dg_inv _ _ _ _ _ _ (mul_one 1) (inv_mul_cancel₀ ha0) (mul_inv_cancel₀ ha0))
    (tM2_det ha0) (tM2_unit h ha0 hbar)

theorem tSU1_mat (h : UnitaryFieldData p 1 K) {a : K} (ha0 : a ≠ 0) (hbar : h.bar a = a⁻¹) :
    ((tSU1 h ha0 hbar : GL (Fin 3) K) : M3 K) = dg a a⁻¹ 1 := rfl

theorem tSU2_mat (h : UnitaryFieldData p 1 K) {a : K} (ha0 : a ≠ 0) (hbar : h.bar a = a⁻¹) :
    ((tSU2 h ha0 hbar : GL (Fin 3) K) : M3 K) = dg 1 a a⁻¹ := rfl

theorem z0M_comm_dg (x y z : K) : z0M * dg x y z = dg x y z * z0M := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [z0M, dg, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

theorem z0M_comm_wM : (z0M : M3 K) * wM = wM * z0M := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [z0M, wM, Matrix.mul_apply, Fin.sum_univ_three]

theorem z0SU_comm_tSU1 (h : UnitaryFieldData p 1 K) {a : K} (ha0 : a ≠ 0)
    (hbar : h.bar a = a⁻¹) : z0SU h * tSU1 h ha0 hbar = tSU1 h ha0 hbar * z0SU h := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, z0SU_mat, tSU1_mat]
  exact z0M_comm_dg _ _ _

theorem z0SU_comm_tSU2 (h : UnitaryFieldData p 1 K) {a : K} (ha0 : a ≠ 0)
    (hbar : h.bar a = a⁻¹) : z0SU h * tSU2 h ha0 hbar = tSU2 h ha0 hbar * z0SU h := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, z0SU_mat, tSU2_mat]
  exact z0M_comm_dg _ _ _

theorem z0SU_comm_wSU (h : UnitaryFieldData p 1 K) :
    z0SU h * wSU h = wSU h * z0SU h := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, z0SU_mat, wSU_mat]
  exact z0M_comm_wM

theorem uout_P (h : UnitaryFieldData p 1 K) (hp : p.Prime) (hp13 : 13 ≤ p) (hp4 : p % 4 = 1)
    (S : Subgroup (unitaryPSU h 3)) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    UOut (unitaryPSU h 3)
      (Subgroup.centralizer ((S ⊓ Subgroup.centralizer (S : Set (unitaryPSU h 3)) :
        Subgroup (unitaryPSU h 3)) : Set (unitaryPSU h 3))) := by
  haveI := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  intro y hy hfix
  obtain ⟨a', ha', ha3, ha6⟩ := exists_good_a h hp13
  have ha0 : a' ≠ 0 := by rintro rfl; simp at ha'
  have hbar' : h.bar a' = a'⁻¹ := eq_inv_of_mul_eq_one_left ha'
  have ha4 : (unitaryProj h 3 (iSU h)) ^ 4 = 1 := by rw [← map_pow, iSU_pow_four, map_one]
  have hb2 : (unitaryProj h 3 (wSU h)) ^ 2 = 1 := by rw [← map_pow, sq, wSU_sq', map_one]
  have hba : unitaryProj h 3 (wSU h) * unitaryProj h 3 (iSU h) * unitaryProj h 3 (wSU h) =
      (unitaryProj h 3 (iSU h))⁻¹ := by
    rw [← map_mul, ← map_mul, wSU_iSU_wSU, ← map_inv, iSU_inv_eq]
  have hQ : IsPGroup 2 (Subgroup.closure ({unitaryProj h 3 (iSU h), unitaryProj h 3 (wSU h)} :
      Set (unitaryPSU h 3))) :=
    isPGroup_two_dihedral_closure ha4 hb2 hba
  obtain ⟨S', hQS', hS'⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf_of_le
    (le_top : Subgroup.closure ({unitaryProj h 3 (iSU h), unitaryProj h 3 (wSU h)} :
      Set (unitaryPSU h 3)) ≤ ⊤) hQ
  obtain ⟨k, hk⟩ := CFSG.Quasithin.H13.exists_conj_of_isSylowTwoOf_top_cs5 hS hS'
  have haS' : unitaryProj h 3 (iSU h) ∈ S' :=
    hQS' (Subgroup.subset_closure (by simp))
  have hbS' : unitaryProj h 3 (wSU h) ∈ S' :=
    hQS' (Subgroup.subset_closure (by simp))
  have hcentre : ∀ m ∈ S' ⊓ Subgroup.centralizer (S' : Set (unitaryPSU h 3)),
      m = 1 ∨ m = unitaryProj h 3 (z0SU h) := by
    intro m hm
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hm
    exact center_sub_z0 h hp hp4 hS'.isPGroup haS' hbS' hm.1 hm.2
  have hz1 : unitaryProj h 3 (z0SU h) * unitaryProj h 3 (tSU1 h ha0 hbar') =
      unitaryProj h 3 (tSU1 h ha0 hbar') * unitaryProj h 3 (z0SU h) := by
    rw [← map_mul, ← map_mul, z0SU_comm_tSU1]
  have hz2 : unitaryProj h 3 (z0SU h) * unitaryProj h 3 (tSU2 h ha0 hbar') =
      unitaryProj h 3 (tSU2 h ha0 hbar') * unitaryProj h 3 (z0SU h) := by
    rw [← map_mul, ← map_mul, z0SU_comm_tSU2]
  have hz3 : unitaryProj h 3 (z0SU h) * unitaryProj h 3 (wSU h) =
      unitaryProj h 3 (wSU h) * unitaryProj h 3 (z0SU h) := by
    rw [← map_mul, ← map_mul, z0SU_comm_wSU]
  have key : ∀ n : unitaryPSU h 3, unitaryProj h 3 (z0SU h) * n = n * unitaryProj h 3 (z0SU h) →
      k⁻¹ * n * k ∈ Subgroup.centralizer ((S ⊓ Subgroup.centralizer (S : Set (unitaryPSU h 3)) :
        Subgroup (unitaryPSU h 3)) : Set (unitaryPSU h 3)) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hm' : m ∈ S ⊓ Subgroup.centralizer (S : Set (unitaryPSU h 3)) := hm
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hm'
    have hkm : k * m * k⁻¹ ∈ S' ⊓ Subgroup.centralizer (S' : Set (unitaryPSU h 3)) := by
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      constructor
      · rw [hk]
        exact Subgroup.mem_map.mpr ⟨m, hm'.1, rfl⟩
      · intro s hs
        rw [hk] at hs
        obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
        have hc := hm'.2 s₀ hs₀
        show k * s₀ * k⁻¹ * (k * m * k⁻¹) = k * m * k⁻¹ * (k * s₀ * k⁻¹)
        calc k * s₀ * k⁻¹ * (k * m * k⁻¹) = k * (s₀ * m) * k⁻¹ := by group
          _ = k * (m * s₀) * k⁻¹ := by rw [hc]
          _ = k * m * k⁻¹ * (k * s₀ * k⁻¹) := by group
    have hmn : (k * m * k⁻¹) * n = n * (k * m * k⁻¹) := by
      rcases hcentre _ hkm with h1 | h1
      · rw [h1, one_mul, mul_one]
      · rw [h1]
        exact hn
    calc m * (k⁻¹ * n * k) = k⁻¹ * ((k * m * k⁻¹) * n) * k := by group
      _ = k⁻¹ * (n * (k * m * k⁻¹)) * k := by rw [hmn]
      _ = k⁻¹ * n * k * m := by group
  set y' : MulAut (unitaryPSU h 3) := MulAut.conj k * y * MulAut.conj k⁻¹ with hy'
  have hy'2 : y' * y' = 1 := by
    rw [hy', map_inv]
    calc (MulAut.conj k * y * (MulAut.conj k)⁻¹) * (MulAut.conj k * y * (MulAut.conj k)⁻¹)
        = MulAut.conj k * (y * y) * (MulAut.conj k)⁻¹ := by group
      _ = 1 := by rw [hy, mul_one, mul_inv_cancel]
  have hfixn : ∀ n : unitaryPSU h 3, unitaryProj h 3 (z0SU h) * n = n * unitaryProj h 3 (z0SU h) →
      y' n = n := by
    intro n hn
    have hmem := hfix _ (key n hn)
    rw [hy']
    simp only [MulAut.mul_apply, MulAut.conj_apply, inv_inv]
    rw [hmem]
    group
  have hq : 2 < p ^ 1 := by rw [pow_one]; omega
  obtain ⟨x, hx⟩ := core_u3 h hq ha' ha3 ha6 (tSU1 h ha0 hbar') (tSU2 h ha0 hbar') (wSU h)
    (tSU1_mat h ha0 hbar') (tSU2_mat h ha0 hbar') (wSU_mat h) y' hy'2
    (hfixn _ hz1) (hfixn _ hz2) (hfixn _ hz3)
  refine ⟨k⁻¹ * x * k, ?_⟩
  have hyk : y = MulAut.conj k⁻¹ * y' * MulAut.conj k := by rw [hy', map_inv]; group
  rw [hyk, hx, ← map_mul, ← map_mul]

theorem uout_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (S : Subgroup X)
    (hY : UOut Y (Subgroup.centralizer ((S.map e.toMonoidHom ⊓
      Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) : Subgroup Y) : Set Y))) :
    UOut X (Subgroup.centralizer ((S ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) :
      Set X)) := by
  intro y hy hfix
  have hyy : ∀ x, y (y x) = x := fun x => by
    have := congrArg (fun f : MulAut X => f x) hy
    simpa using this
  set y' : MulAut Y := (e.symm.trans y).trans e with hy'
  have hy'2 : y' * y' = 1 := by
    ext z
    simp [hy', MulEquiv.trans_apply, hyy]
  have hfix' : ∀ n ∈ Subgroup.centralizer ((S.map e.toMonoidHom ⊓
      Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) : Subgroup Y) : Set Y),
      y' n = n := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff] at hn
    have hx : e.symm n ∈ Subgroup.centralizer ((S ⊓ Subgroup.centralizer (S : Set X) :
        Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hm' : m ∈ S ⊓ Subgroup.centralizer (S : Set X) := hm
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hm'
      have hmY : e m ∈ S.map e.toMonoidHom ⊓
          Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) := by
        rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
        constructor
        · exact Subgroup.mem_map.mpr ⟨m, hm'.1, rfl⟩
        · intro s hs
          obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
          have hc := hm'.2 s₀ hs₀
          show e s₀ * e m = e m * e s₀
          rw [← map_mul, ← map_mul, hc]
      have h1 := hn (e m) hmY
      have h2 := congrArg e.symm h1
      simpa [map_mul] using h2
    have hfx := hfix _ hx
    show e (y (e.symm n)) = n
    rw [hfx]
    simp
  obtain ⟨x', hx'⟩ := hY y' hy'2 hfix'
  refine ⟨e.symm x', ?_⟩
  ext z
  have h1 : y' (e z) = e (y z) := by simp [hy']
  have h2 : y z = e.symm (y' (e z)) := by rw [h1]; simp
  rw [h2, hx', MulAut.conj_apply, MulAut.conj_apply]
  simp [map_mul, map_inv]

theorem nk_u3odd_out : NKLeafU3OddOut := by
  unfold NKLeafU3OddOut
  intro p hpp hp13 hp4 X _ hX S hS
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hU : UnitaryFieldData p 1 K := ⟨hpp, le_rfl, by rw [hK]; ring⟩
  let ι : X ≃* unitaryPSU hU 3 := e.trans (unitaryPSUEquiv hU (by norm_num)).symm
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf (S.map ι.toMonoidHom) ⊤ :=
    (CFSG.Quasithin.H13.isSylowTwoOf_top_map_mulEquiv_cs5 ι S).mpr hS
  exact uout_of_mulEquiv ι S (uout_P hU hpp hp13 hp4 _ hS')

end CFSG.Quasithin.H13.L829NK.U3Out
