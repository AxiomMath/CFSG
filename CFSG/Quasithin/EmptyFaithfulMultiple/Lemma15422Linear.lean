module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Core
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F6 Matrix

namespace L15422

section Matrix

variable {F : Type*} [Field F]

theorem sq_eq_neg_one_of_sq_eq_scalar {A : Matrix (Fin 2) (Fin 2) F} (hdet : A.det = 1) {r : F}
    (hA : A * A = Matrix.scalar (Fin 2) r) (hns : ∀ t : F, A ≠ Matrix.scalar (Fin 2) t) :
    A * A = -1 ∧ A 0 0 + A 1 1 = 0 := by
  have h00 := congrFun (congrFun hA 0) 0
  have h01 := congrFun (congrFun hA 0) 1
  have h10 := congrFun (congrFun hA 1) 0
  have h11 := congrFun (congrFun hA 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  rw [Matrix.det_fin_two] at hdet
  by_cases htr : A 0 0 + A 1 1 = 0
  · refine ⟨?_, htr⟩
    have hd : A 1 1 = -A 0 0 := by linear_combination htr
    have hr : r = -1 := by
      rw [hd] at hdet
      linear_combination -h00 - hdet
    rw [hA, hr]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · exfalso
    have hb : A 0 1 = 0 := by
      have : A 0 1 * (A 0 0 + A 1 1) = 0 := by linear_combination h01
      exact (mul_eq_zero.mp this).resolve_right htr
    have hc : A 1 0 = 0 := by
      have : A 1 0 * (A 0 0 + A 1 1) = 0 := by linear_combination h10
      exact (mul_eq_zero.mp this).resolve_right htr
    have had : A 0 0 = A 1 1 := by
      have : (A 0 0 - A 1 1) * (A 0 0 + A 1 1) = 0 := by
        rw [hb] at h00
        rw [hc] at h11
        linear_combination h00 - h11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right htr)
    apply hns (A 0 0)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, had]

end Matrix

section PSL

variable {F : Type*} [Field F]

theorem exists_orderOf_three_normalized (h2 : (2 : F) ≠ 0) {s : F} (hs : s ^ 2 = 3)
    (h3 : (3 : F) ≠ 0) {a : ProjectiveSpecialLinearGroup (Fin 2) F} (ha : a ^ 2 = 1) (ha1 : a ≠ 1) :
    ∃ x : ProjectiveSpecialLinearGroup (Fin 2) F, x ^ 3 = 1 ∧ x ≠ 1 ∧ x * a = a * x ∧
      ∀ y : ProjectiveSpecialLinearGroup (Fin 2) F, y * a = a * y →
        y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x⁻¹ := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective a
  have hA2 : A ^ 2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using ha
  obtain ⟨r, -, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA2
  have hns : ∀ t : F, (A : Matrix (Fin 2) (Fin 2) F) ≠ Matrix.scalar (Fin 2) t := by
    intro t ht
    apply ha1
    rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨t, ?_, ht.symm⟩
    have hd := A.2
    rw [ht, Matrix.det_fin_two] at hd
    simpa [sq] using hd
  have hAr : (A : Matrix (Fin 2) (Fin 2) F) * A = Matrix.scalar (Fin 2) r := by
    rw [hrA, Matrix.SpecialLinearGroup.coe_pow, sq]
  obtain ⟨hAA, htr⟩ := sq_eq_neg_one_of_sq_eq_scalar A.2 hAr hns
  have hdetA : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact A.2
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply h3
    rw [← hs]
    ring
  set X : Matrix (Fin 2) (Fin 2) F := (-(1/2) : F) • 1 + (s / 2) • (A : Matrix (Fin 2) (Fin 2) F)
    with hXdef
  set Y : Matrix (Fin 2) (Fin 2) F := (-(1/2) : F) • 1 - (s / 2) • (A : Matrix (Fin 2) (Fin 2) F)
    with hYdef
  have hdetX : X.det = 1 := by
    rw [Matrix.det_fin_two, hXdef]
    simp
    field_simp
    linear_combination (-s) * htr + s ^ 2 * hdetA + hs
  have hdetY : Y.det = 1 := by
    rw [Matrix.det_fin_two, hYdef]
    simp
    field_simp
    linear_combination s * htr + s ^ 2 * hdetA + hs
  have hXY : X * Y = 1 := by
    rw [hXdef, hYdef]
    simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hAA]
    match_scalars
    · field_simp
      linear_combination hs
    · field_simp
      ring
  have hYX : Y * X = 1 := by
    rw [hXdef, hYdef]
    simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hAA]
    match_scalars
    · field_simp
      linear_combination hs
    · field_simp
      ring
  have hXX : X * X = Y := by
    rw [hXdef, hYdef]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hAA]
    match_scalars
    · field_simp
      linear_combination -hs
    · field_simp
      ring
  have hXA : X * A = A * X := by
    rw [hXdef]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  let Xs : SpecialLinearGroup (Fin 2) F := ⟨X, hdetX⟩
  let Ys : SpecialLinearGroup (Fin 2) F := ⟨Y, hdetY⟩
  have hXYs : Xs * Ys = 1 := Subtype.ext hXY
  have hYs : Ys = Xs⁻¹ := (eq_inv_of_mul_eq_one_right hXYs)
  have hXs3 : Xs ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    change X ^ 3 = 1
    rw [pow_succ, sq, hXX, hYX]
  have hXsA : Xs * A = A * Xs := Subtype.ext hXA
  refine ⟨(Xs : ProjectiveSpecialLinearGroup (Fin 2) F), ?_, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_pow, hXs3, QuotientGroup.mk_one]
  · intro hX1
    rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff] at hX1
    obtain ⟨t, -, ht⟩ := hX1
    have e01 := congrFun (congrFun ht 0) 1
    have e10 := congrFun (congrFun ht 1) 0
    have e00 := congrFun (congrFun ht 0) 0
    have e11 := congrFun (congrFun ht 1) 1
    change _ = X 0 1 at e01
    change _ = X 1 0 at e10
    change _ = X 0 0 at e00
    change _ = X 1 1 at e11
    simp [hXdef, hs0, h2] at e01 e10 e00 e11
    apply hns (A 0 0)
    have h00 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = A 0 0 := by
      have : s / 2 * ((A : Matrix (Fin 2) (Fin 2) F) 1 1 - A 0 0) = 0 := by
        linear_combination e00 - e11
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (div_ne_zero hs0 h2)
      · exact (sub_eq_zero.mp h)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e01, e10, h00]
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hXsA]
  · intro y hy
    obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Matrix.SpecialLinearGroup.mem_center_iff] at hy
    obtain ⟨r', hr', hr'B⟩ := hy
    have hAB : (A : Matrix (Fin 2) (Fin 2) F) * B = r' • ((B : Matrix (Fin 2) (Fin 2) F) * A) := by
      have h1 : A * B = (B * A) * ((B * A)⁻¹ * (A * B)) := by group
      have h2 : ((A * B : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          ((B * A * ((B * A)⁻¹ * (A * B)) : SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) := by rw [← h1]
      rw [Matrix.SpecialLinearGroup.coe_mul (B * A) ((B * A)⁻¹ * (A * B)), ← hr'B,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
      rw [h2, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, mul_smul_comm, mul_one]
    have hBX : (B : Matrix (Fin 2) (Fin 2) F) * X =
        ((-(1/2) : F) • 1 + (r' * (s / 2)) • (A : Matrix (Fin 2) (Fin 2) F)) * B := by
      rw [hXdef]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hAB, smul_smul]
      congr 1
      rw [show r' * (s / 2) * r' = (s / 2) * r' ^ 2 by ring]
      simp only [Fintype.card_fin] at hr'
      rw [hr', mul_one]
    have hr'' : r' = 1 ∨ r' = -1 := by
      simp only [Fintype.card_fin] at hr'
      have : (r' - 1) * (r' + 1) = 0 := by linear_combination hr'
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rcases hr'' with rfl | rfl
    · left
      have : B * Xs * B⁻¹ = Xs := by
        rw [mul_inv_eq_iff_eq_mul]
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
        change (B : Matrix (Fin 2) (Fin 2) F) * X = X * B
        rw [hBX, one_mul]
      rw [this]
    · right
      have : B * Xs * B⁻¹ = Xs⁻¹ := by
        rw [mul_inv_eq_iff_eq_mul, ← hYs]
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
        change (B : Matrix (Fin 2) (Fin 2) F) * X = Y * B
        rw [hBX, hYdef]
        congr 1
        module
      rw [this, QuotientGroup.mk_inv]

end PSL

section Exclusion

variable {H : Type*} [Group H] [Finite H]

theorem eq_bot_of_charTwo_of_odd {M R : Subgroup H} (hM : CFSG.QuasithinUnique.CharTwo M)
    (hRM : R ≤ M) (hMR : M ≤ Subgroup.normalizer (R : Set H)) (hR : Odd (Nat.card R)) :
    R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 M
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hPM : P ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hMP : M ≤ Subgroup.normalizer (P : Set H) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hRP : R ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨j, hj⟩ := hP2 ⟨x, hx.2⟩
    have h1 : orderOf x ∣ 2 ^ j :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hj)
    have h2 : orderOf x ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨x, hx.1⟩ : R)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ j) (Nat.card R) :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hR)
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2))
  have hRc : R ≤ Subgroup.centralizer (P : Set H) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hc : r * q * r⁻¹ * q⁻¹ ∈ R ⊓ P := by
      refine ⟨?_, ?_⟩
      · have : q * r⁻¹ * q⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (hMR (hPM hq)) _).mp (R.inv_mem hr)
        have e : r * q * r⁻¹ * q⁻¹ = r * (q * r⁻¹ * q⁻¹) := by group
        rw [e]
        exact R.mul_mem hr this
      · have : r * q * r⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hMP (hRM hr)) _).mp hq
        exact P.mul_mem this (P.inv_mem hq)
    rw [hRP, Subgroup.mem_bot] at hc
    calc q * r = r * q * r⁻¹ * q⁻¹ * (q * r) := by rw [hc, one_mul]
      _ = r * q := by group
  rw [eq_bot_iff, ← hRP]
  exact le_inf le_rfl fun x hx => hM ⟨hRM hx, hRc hx⟩

theorem exists_mul_ne_of_simple {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (h2 : 2 ∣ Nat.card X) (h3 : 3 ∣ Nat.card X) : ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := h }
  have hp := IsSimpleGroup.prime_card (α := X)
  have e2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
  have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
  omega

omit [Finite H] in
theorem exists_psl_of_isL2FieldExt {W : Type} [Group W] {p : ℕ} (hL : IsL2FieldExt p W) :
    p.Prime ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = p ^ 2 ∧
      ∃ N₀ : Subgroup W, N₀.index = 2 ∧
        Nonempty (↥N₀ ≃* ProjectiveSpecialLinearGroup (Fin 2) F) := by
  obtain ⟨hp, F, hF, hFin, hcard, N₀, e, -, -, hidx, -, -⟩ := hL
  let _ : Fintype F := Fintype.ofFinite F
  refine ⟨hp, F, hF, inferInstance, by rw [← Nat.card_eq_fintype_card]; exact hcard, N₀, hidx,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩⟩

omit [Finite H] in
theorem oTwoUpper_le_of_index_eq_two {D : Type*} [Group D] {N₀ : Subgroup D}
    (hidx : N₀.index = 2) : oTwoUpper (⊤ : Subgroup D) ≤ N₀ := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨k, hk⟩ := hx.2
  have hx1 : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hsq := Subgroup.sq_mem_of_index_two hidx x
  have : x = (x ^ 2)⁻¹ ^ k := by
    calc x = x * (x ^ (2 * k + 1))⁻¹ := by rw [hx1, inv_one, mul_one]
      _ = (x ^ 2)⁻¹ ^ k := by group
  rw [this]
  exact N₀.pow_mem (N₀.inv_mem hsq) k

theorem exists_sq_eq_three {F : Type*} [Field F] [Fintype F] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hcard : Fintype.card F = p ^ 2) [CharP F p] (h3 : (3 : F) ≠ 0) :
    ∃ s : F, s ^ 2 = 3 := by
  have hpow : (3 : F) ^ p = 3 := by
    have := map_ofNat (frobenius F p) 3
    rwa [frobenius_def] at this
  have hpow1 : (3 : F) ^ (p - 1) = 1 := by
    have hp1 : p = (p - 1) + 1 := (Nat.succ_pred_eq_of_pos hp.out.pos).symm
    rw [hp1, pow_succ] at hpow
    exact mul_right_cancel₀ h3 (hpow.trans (one_mul 3).symm)
  have hring : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2
  have hdiv : p ^ 2 / 2 = (p - 1) * (k + 1) := by
    have hk' : p - 1 = 2 * k := by omega
    rw [hk', hk, show (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 by ring,
      Nat.mul_add_div (by norm_num : 0 < 2)]
    simp [mul_assoc]
  obtain ⟨r, hr⟩ := (FiniteField.isSquare_iff hring h3).mpr (by
    rw [hcard, hdiv, pow_mul, hpow1, one_pow])
  exact ⟨r, by rw [sq, ← hr]⟩

theorem false_of_isL2FieldExt {H : Type} [Group H] [Finite H] {N : Subgroup H} [hN : N.Normal]
    (hQN : IsSylowIn 2 (Open.pCore 2 H) N)
    (hO : ∀ B : Subgroup H, B.Normal → Odd (Nat.card B) → B = ⊥)
    (hnc : ¬ Subgroup.centralizer (Open.pCore 2 H : Set H) ≤ Open.pCore 2 H)
    (hQD : Open.pCore 2 (H ⧸ N) = ⊥) {u : H} (hu2 : u ^ 2 = 1)
    (hu1 : QuotientGroup.mk' N u ≠ 1)
    (huO : QuotientGroup.mk' N u ∈ oTwoUpper (⊤ : Subgroup (H ⧸ N)))
    (huc : CFSG.QuasithinUnique.CharTwo (Subgroup.centralizer ({u} : Set H)))
    {p : ℕ} (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hL : IsL2FieldExt p (H ⧸ N)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, F, hF, hFin, hcardF, N₀, hidx, ⟨e⟩⟩ := exists_psl_of_isL2FieldExt hL
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP F p := charP_of_card_eq_prime_pow hcardF
  have h2 : (2 : F) ≠ 0 := by
    have : ((2 : ℕ) : F) ≠ 0 := fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((CharP.cast_eq_zero_iff F p 2).mp h))
    exact_mod_cast this
  have h3 : (3 : F) ≠ 0 := by
    have : ((3 : ℕ) : F) ≠ 0 := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        ((CharP.cast_eq_zero_iff F p 3).mp h))
    exact_mod_cast this
  obtain ⟨s, hs⟩ := exists_sq_eq_three hp2 hcardF h3
  set π := QuotientGroup.mk' N
  have hcard4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hcardF]
    have : 2 ≤ p := hp.two_le
    nlinarith
  have hsimp : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard4
  have hN₀s : IsSimpleGroup N₀ := e.isSimpleGroup
  have huN₀ : π u ∈ N₀ := oTwoUpper_le_of_index_eq_two hidx huO
  set a := e ⟨π u, huN₀⟩ with hadef
  have ha2 : a ^ 2 = 1 := by
    rw [hadef, ← map_pow]
    have : (⟨π u, huN₀⟩ : N₀) ^ 2 = 1 := Subtype.ext (by simp [← map_pow, hu2])
    rw [this, map_one]
  have ha1 : a ≠ 1 := by
    rw [hadef, Ne, MulEquivClass.map_eq_one_iff]
    exact fun h => hu1 (congrArg Subtype.val h)
  obtain ⟨x, hx3, hx1, hxa, hxn⟩ := exists_orderOf_three_normalized h2 hs h3 ha2 ha1
  set xs : H ⧸ N := ((e.symm x : N₀) : H ⧸ N) with hxsdef
  have hxsN₀ : xs ∈ N₀ := (e.symm x).2
  have hxs3 : xs ^ 3 = 1 := by
    rw [hxsdef, ← Subgroup.coe_pow, ← map_pow, hx3, map_one, Subgroup.coe_one]
  have hxs1 : xs ≠ 1 := by
    intro h
    apply hx1
    have : e.symm x = 1 := Subtype.ext h
    rw [← e.apply_symm_apply x, this, map_one]
  have hxsu : xs * π u = π u * xs := by
    have h1 := congrArg e.symm hxa
    rw [map_mul, map_mul, hadef, e.symm_apply_apply] at h1
    exact congrArg Subtype.val h1
  have hxsn : ∀ y ∈ N₀, y * π u = π u * y → y * xs * y⁻¹ = xs ∨ y * xs * y⁻¹ = xs⁻¹ := by
    intro y hy hyu
    have hya : e ⟨y, hy⟩ * a = a * e ⟨y, hy⟩ := by
      rw [hadef, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hyu
    rcases hxn _ hya with h | h
    · left
      have h1 := congrArg e.symm h
      rw [map_mul, map_mul, map_inv, e.symm_apply_apply] at h1
      exact congrArg Subtype.val h1
    · right
      have h1 := congrArg e.symm h
      rw [map_mul, map_mul, map_inv, map_inv, e.symm_apply_apply] at h1
      exact congrArg Subtype.val h1
  have hxso : orderOf xs = 3 := orderOf_eq_prime hxs3 hxs1
  have hN₀nab : ∃ b c : N₀, b * c ≠ c * b := by
    have h2d : 2 ∣ Nat.card N₀ := by
      have := orderOf_dvd_natCard (⟨π u, huN₀⟩ : N₀)
      rwa [Subgroup.orderOf_mk, orderOf_eq_prime (by rw [← map_pow, hu2, map_one]) hu1] at this
    have h3d : 3 ∣ Nat.card N₀ := by
      have := orderOf_dvd_natCard (e.symm x)
      rwa [← Subgroup.orderOf_coe, ← hxsdef, hxso] at this
    exact exists_mul_ne_of_simple h2d h3d
  obtain ⟨K, hKn, hKmap, hKN, hKC, -, hNK⟩ := exists_layer hQN hO hnc hQD hidx hN₀s hN₀nab
  have hZ2 : IsPGroup 2 ↥(K ⊓ N) := (CFSG.LieType.BorelTits.pCore_isPGroup 2).to_le hKN
  have hZc : ∀ c ∈ K ⊓ N, ∀ k ∈ K, c * k = k * c := fun c hc k hk =>
    ((Subgroup.mem_centralizer_iff.mp (hKC hk)) c (hKN hc))
  have hcube : ∀ y ∈ K, ∀ z ∈ K, π y = π z → y ^ 3 = 1 → z ^ 3 = 1 → y = z := by
    intro y hy z hz hyz hy3 hz3
    have hd : y⁻¹ * z ∈ K ⊓ N := by
      refine ⟨K.mul_mem (K.inv_mem hy) hz, (QuotientGroup.eq_one_iff _).mp ?_⟩
      change π (y⁻¹ * z) = 1
      rw [map_mul, map_inv, hyz, inv_mul_cancel]
    have hcomm : y * (y⁻¹ * z) = (y⁻¹ * z) * y := (hZc _ hd y hy).symm
    have hd3 : (y⁻¹ * z) ^ 3 = 1 := by
      have : z ^ 3 = y ^ 3 * (y⁻¹ * z) ^ 3 := by
        rw [← Commute.mul_pow hcomm]
        group
      rw [hy3, hz3, one_mul] at this
      exact this.symm
    obtain ⟨j, hj⟩ := hZ2 ⟨_, hd⟩
    have h1 : orderOf (y⁻¹ * z) ∣ 2 ^ j :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hj)
    have h2' : orderOf (y⁻¹ * z) ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
    have hcop : Nat.Coprime (2 ^ j) 3 := Nat.Coprime.pow_left j (by norm_num)
    exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2'))
  obtain ⟨x₀, hx₀K, hx₀⟩ : xs ∈ K.map π := hKmap ▸ hxsN₀
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hZ2
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.card ↥(K ⊓ N) := ⟨_, rfl⟩
  obtain ⟨x', hx'def⟩ : ∃ x', x' = x₀ ^ m := ⟨_, rfl⟩
  have hx'K : x' ∈ K := hx'def ▸ K.pow_mem hx₀K m
  have hx'3 : x' ^ 3 = 1 := by
    have hx₀3 : x₀ ^ 3 ∈ K ⊓ N := by
      refine ⟨K.pow_mem hx₀K 3, (QuotientGroup.eq_one_iff _).mp ?_⟩
      change π (x₀ ^ 3) = 1
      rw [map_pow, hx₀, hxs3]
    have := pow_card_eq_one' (G := ↥(K ⊓ N)) (x := ⟨_, hx₀3⟩)
    rw [hx'def, ← pow_mul, mul_comm, pow_mul, hm]
    simpa using congrArg Subtype.val this
  have hπx' : π x' = xs ^ m := by rw [hx'def, map_pow, hx₀]
  have hx'1 : x' ≠ 1 := by
    intro h
    have : xs ^ m = 1 := by rw [← hπx', h, map_one]
    have hd := orderOf_dvd_of_pow_eq_one this
    rw [hxso, hm, hj] at hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  obtain ⟨k, hkK, hk⟩ : π u ∈ K.map π := hKmap ▸ huN₀
  have hn : k⁻¹ * u ∈ N := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    change π (k⁻¹ * u) = 1
    rw [map_mul, map_inv, hk, inv_mul_cancel]
  have hconj : ∀ y ∈ K, u * y * u⁻¹ = k * y * k⁻¹ := by
    intro y hy
    have hny : (k⁻¹ * u) * y = y * (k⁻¹ * u) :=
      ((Subgroup.mem_centralizer_iff.mp (hNK hn)) y hy).symm
    calc u * y * u⁻¹ = k * ((k⁻¹ * u) * y) * (k⁻¹ * u)⁻¹ * k⁻¹ := by group
      _ = k * (y * (k⁻¹ * u)) * (k⁻¹ * u)⁻¹ * k⁻¹ := by rw [hny]
      _ = k * y * k⁻¹ := by group
  have hx'u : u * x' * u⁻¹ = x' := by
    rw [hconj x' hx'K]
    refine (hcube x' hx'K _ (K.mul_mem (K.mul_mem hkK hx'K) (K.inv_mem hkK)) ?_ hx'3 ?_).symm
    · rw [map_mul, map_mul, map_inv, hk, hπx']
      have : π u * xs ^ m * (π u)⁻¹ = xs ^ m := by
        rw [← (Commute.pow_left hxsu m).eq]
        group
      rw [this]
    · rw [conj_pow, hx'3]
      group
  set M := K ⊓ Subgroup.centralizer ({u} : Set H)
  have hRM : Subgroup.zpowers x' ≤ M := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨hx'K, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc x' * u = u * x' * u⁻¹ * u := by rw [hx'u]
      _ = u * x' := by group
  have hMR : M ≤ Subgroup.normalizer (Subgroup.zpowers x' : Set H) := by
    intro y hy
    have hyu : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hyπ : π y ∈ N₀ := hKmap ▸ Subgroup.mem_map_of_mem π hy.1
    have hyx : y * x' * y⁻¹ = x' ∨ y * x' * y⁻¹ = x'⁻¹ := by
      have hc3 : (y * x' * y⁻¹) ^ 3 = 1 := by rw [conj_pow, hx'3]; group
      have hK' : y * x' * y⁻¹ ∈ K := K.mul_mem (K.mul_mem hy.1 hx'K) (K.inv_mem hy.1)
      have hyu' : π y * π u = π u * π y := by rw [← map_mul, ← map_mul, hyu]
      rcases hxsn (π y) hyπ hyu' with h | h
      · left
        refine (hcube x' hx'K _ hK' ?_ hx'3 hc3).symm
        rw [map_mul, map_mul, map_inv, hπx', ← conj_pow, h]
      · right
        refine (hcube x'⁻¹ (K.inv_mem hx'K) _ hK' ?_ (by rw [inv_pow, hx'3, inv_one]) hc3).symm
        rw [map_mul, map_mul, map_inv, map_inv, hπx', ← conj_pow, h, inv_pow]
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← conj_zpow]
      rcases hyx with h | h <;> rw [h]
      · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x') n
      · exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x')) n
    · intro hw
      obtain ⟨n, hn'⟩ := Subgroup.mem_zpowers_iff.mp hw
      have : w = y⁻¹ * x' ^ n * y := by rw [hn']; group
      rw [this]
      have hyx' : y⁻¹ * x' * y = x' ∨ y⁻¹ * x' * y = x'⁻¹ := by
        rcases hyx with h | h
        · left
          calc y⁻¹ * x' * y = y⁻¹ * (y * x' * y⁻¹) * y := by rw [h]
            _ = x' := by group
        · right
          calc y⁻¹ * x' * y = y⁻¹ * (y * x' * y⁻¹)⁻¹ * y := by rw [h, inv_inv]
            _ = x'⁻¹ := by group
      have e1 : y⁻¹ * x' ^ n * y = (y⁻¹ * x' * y) ^ n := by
        rw [show y⁻¹ * x' * y = y⁻¹ * x' * y⁻¹⁻¹ by rw [inv_inv], conj_zpow, inv_inv]
      rw [e1]
      rcases hyx' with h | h <;> rw [h]
      · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x') n
      · exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x')) n
  have hRodd : Odd (Nat.card (Subgroup.zpowers x')) := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx'3 hx'1]
    decide
  have hMc : CFSG.QuasithinUnique.CharTwo M := by
    refine huc.of_isSubnormal inf_le_right ?_
    have : (M.subgroupOf (Subgroup.centralizer ({u} : Set H))).Normal :=
      ⟨fun z hz g => by
        rw [Subgroup.mem_subgroupOf] at hz ⊢
        exact ⟨hKn.conj_mem _ hz.1 g, (Subgroup.centralizer ({u} : Set H)).mul_mem
          ((Subgroup.centralizer ({u} : Set H)).mul_mem g.2 hz.2)
          ((Subgroup.centralizer ({u} : Set H)).inv_mem g.2)⟩⟩
    exact this.isSubnormal
  have hR := eq_bot_of_charTwo_of_odd hMc hRM hMR hRodd
  exact hx'1 (Subgroup.zpowers_eq_bot.mp hR)

end Exclusion

end L15422

end CFSG.Quasithin.EmptyFaithfulMultiple
