module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.RankThree.Classical.SemilinearFixedBasis
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear

public noncomputable section

namespace CFSG.RankThree.UnitaryDescent

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] def normσ (σ : K ≃+* K) (m : ℕ) (x : K) : K :=
  ∏ i ∈ Finset.range m, (σ ^ i) x

theorem normσ_mul (σ : K ≃+* K) (m : ℕ) (x y : K) :
    normσ σ m (x * y) = normσ σ m x * normσ σ m y := by
  simp only [normσ, map_mul, Finset.prod_mul_distrib]

theorem normσ_pow (σ : K ≃+* K) (m : ℕ) (x : K) (k : ℕ) :
    normσ σ m (x ^ k) = normσ σ m x ^ k := by
  simp only [normσ, map_pow, Finset.prod_pow]

theorem normσ_one (σ : K ≃+* K) (m : ℕ) : normσ σ m 1 = 1 := by
  simp [normσ]

theorem apply_normσ (σ : K ≃+* K) {m : ℕ} (hm : σ ^ m = 1) (x : K) :
    σ (normσ σ m x) = normσ σ m x := by
  have h1 : σ (normσ σ m x) = ∏ i ∈ Finset.range m, (σ ^ (i + 1)) x := by
    rw [normσ, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_succ']
    rfl
  rw [h1]
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [normσ, map_zero]
  · have h2 : ∏ i ∈ Finset.range (m + 1), (σ ^ i) x =
        (∏ i ∈ Finset.range m, (σ ^ (i + 1)) x) * x := by
      rw [Finset.prod_range_succ']
      rfl
    have h3 : ∏ i ∈ Finset.range (m + 1), (σ ^ i) x = (∏ i ∈ Finset.range m, (σ ^ i) x) * x := by
      rw [Finset.prod_range_succ, hm]
      rfl
    exact mul_right_cancel₀ hx (h2.symm.trans h3)

theorem pow_pow_eq_self {x : K} {N : ℕ} (hx : x ^ N = x) (m : ℕ) : x ^ (N ^ m) = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_mul, ih, hx]

theorem fixed_field_facts (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : K ≃+* K) (hσ : orderOf σ = p) :
    p ∣ f ∧ Nat.card (semilinearFixedSubfield σ) = (ℓ ^ (f / p)) ^ 2 ∧
      ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ (f / p)) := by
  have : Finite K := h.finite
  have h2f : 1 ≤ 2 * f := by have := h.one_le; omega
  obtain ⟨-, -, -, -, -, hA⟩ := finite_field_automorphism_fixed_field_cardinality h.prime h2f h.card
  obtain ⟨hdvd, S, hS, hScard⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσ] at hdvd hScard
  have hpf : p ∣ f :=
    (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).2 hp2) hdvd)
  have hK₀S : semilinearFixedSubfield σ = S := by
    apply SetLike.ext'
    rw [hS]
    ext x
    constructor
    · intro hx τ hτ
      have hx' : σ x = x := RingHom.mem_eqLocusField.mp hx
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
      have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) x :=
        (Subgroup.zpowers_le (H := MulAction.stabilizer (K ≃+* K) x)).mpr hx'
      exact hstab (Subgroup.zpow_mem_zpowers σ m)
    · intro hx
      exact RingHom.mem_eqLocusField.mpr (hx σ (Subgroup.mem_zpowers σ))
  have hcard : Nat.card (semilinearFixedSubfield σ) = (ℓ ^ (f / p)) ^ 2 := by
    rw [hK₀S, hScard, ← pow_mul, Nat.mul_div_assoc _ hpf, mul_comm]
  refine ⟨hpf, hcard, fun x hx => ?_⟩
  have : Finite (semilinearFixedSubfield σ) := Subtype.finite
  have := Fintype.ofFinite (semilinearFixedSubfield σ)
  have hx0 : ((⟨x, RingHom.mem_eqLocusField.mpr hx⟩ : semilinearFixedSubfield σ) ^
      ((ℓ ^ (f / p)) ^ 2)) = ⟨x, RingHom.mem_eqLocusField.mpr hx⟩ := by
    rw [← hcard, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hxq : x ^ ((ℓ ^ (f / p)) ^ 2) = x := by
    have := congrArg Subtype.val hx0
    simpa using this
  obtain ⟨m, hm⟩ := (hp.eq_two_or_odd').resolve_left hp2
  have hq : ℓ ^ f = ((ℓ ^ (f / p)) ^ 2) ^ m * ℓ ^ (f / p) := by
    rw [← pow_mul, ← pow_succ, ← pow_mul, show 2 * m + 1 = p from hm.symm,
      Nat.div_mul_cancel hpf]
  rw [UnitaryFieldData.bar_apply, hq, pow_mul, pow_pow_eq_self hxq]

theorem bar_apply_pow (h : UnitaryFieldData ℓ f K) (σ : K ≃+* K) (i : ℕ) (y : K) :
    h.bar ((σ ^ i) y) = (σ ^ i) (h.bar y) := by
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow]

theorem norm_normσ (h : UnitaryFieldData ℓ f K) (σ : K ≃+* K) (m : ℕ) (x : K) :
    h.norm (normσ σ m x) = normσ σ m (h.norm x) := by
  rw [UnitaryFieldData.norm, normσ, map_prod, ← Finset.prod_mul_distrib, normσ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [bar_apply_pow, UnitaryFieldData.norm, map_mul]

theorem normσ_mem_normOne (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : K ≃+* K) (hσ : orderOf σ = p) {x : K} (hx : h.norm x = 1) :
    σ (normσ σ p x) = normσ σ p x ∧ normσ σ p x ^ (ℓ ^ (f / p) + 1) = 1 := by
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hfix := apply_normσ σ hσp x
  refine ⟨hfix, ?_⟩
  obtain ⟨-, -, hbar⟩ := fixed_field_facts h hp hp2 σ hσ
  have hN : normσ σ p x ^ (ℓ ^ (f / p) + 1) = h.norm (normσ σ p x) := by
    rw [UnitaryFieldData.norm, hbar _ hfix, pow_succ, mul_comm]
  rw [hN, norm_normσ, hx, normσ_one]

theorem exists_normσ_eq (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : K ≃+* K) (hσ : orderOf σ = p) {y : K} (hyσ : σ y = y)
    (hy : y ^ (ℓ ^ (f / p) + 1) = 1) : ∃ x : K, h.norm x = 1 ∧ normσ σ p x = y := by
  obtain ⟨hpf, hcard, hbar⟩ := fixed_field_facts h hp hp2 σ hσ
  have : Finite K := h.finite
  have hfp : 1 ≤ f / p := by
    have := h.one_le
    obtain ⟨k, hk⟩ := hpf
    rw [hk, Nat.mul_div_cancel_left _ hp.pos]
    rcases k with _ | k
    · omega
    · omega
  have h₀ : UnitaryFieldData ℓ (f / p) (semilinearFixedSubfield σ) :=
    ⟨h.prime, hfp, by rw [hcard, ← pow_mul, mul_comm]⟩
  have hu : h₀.norm (⟨y, RingHom.mem_eqLocusField.mpr hyσ⟩ : semilinearFixedSubfield σ) = 1 := by
    rw [UnitaryFieldData.norm_eq_pow]
    apply Subtype.ext
    simpa using hy
  obtain ⟨r, hr0, hr⟩ := h₀.exists_div_bar_eq hu
  have hrK : (r : K) / (r : K) ^ (ℓ ^ (f / p)) = y := by
    have := congrArg Subtype.val hr
    rw [UnitaryFieldData.bar_apply] at this
    simpa using this
  have hr0K : (r : K) ≠ 0 := fun h0 => hr0 (Subtype.ext h0)
  have hσr : σ (r : K) = r := RingHom.mem_eqLocusField.mp r.2
  obtain ⟨d, hd⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ (c := (r : K)⁻¹)
    (by rw [map_inv₀, hσr])
  rw [hσ] at hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h0 : ∏ i ∈ Finset.range p, (σ ^ i) (0 : K) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hp.pos) (by simp)
    rw [h0] at hd
    exact inv_ne_zero hr0K hd.symm
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  refine ⟨d ^ (ℓ ^ f - 1), ?_, ?_⟩
  ·
    have := Fintype.ofFinite K
    have hcardK : Fintype.card K = ℓ ^ f * ℓ ^ f := by
      rw [← Nat.card_eq_fintype_card, h.card, two_mul, pow_add]
    rw [UnitaryFieldData.norm_eq_pow, ← pow_mul]
    have he : (ℓ ^ f - 1) * (ℓ ^ f + 1) = Fintype.card K - 1 := by
      rw [hcardK]
      have : 1 ≤ ℓ ^ f * ℓ ^ f := Nat.one_le_iff_ne_zero.mpr (by positivity)
      zify [hq1, this]
      ring
    rw [he, FiniteField.pow_card_sub_one_eq_one d hd0]
  ·
    rw [normσ_pow, normσ, hd]
    have hrq : (r : K) ^ (ℓ ^ f) = (r : K) ^ (ℓ ^ (f / p)) := by
      rw [← UnitaryFieldData.bar_apply h, hbar _ hσr]
    have hq₀1 : 1 ≤ ℓ ^ (f / p) := Nat.one_le_pow _ _ h.prime.pos
    have e1 : (r : K) ^ (ℓ ^ f - 1) = (r : K) ^ (ℓ ^ (f / p) - 1) := by
      apply mul_right_cancel₀ hr0K
      rw [← pow_succ, ← pow_succ, Nat.sub_add_cancel hq1, Nat.sub_add_cancel hq₀1, hrq]
    rw [inv_pow, e1, ← hrK]
    have e2 : (r : K) ^ (ℓ ^ (f / p)) = (r : K) ^ (ℓ ^ (f / p) - 1) * r := by
      rw [← pow_succ, Nat.sub_add_cancel hq₀1]
    rw [e2]
    field_simp

section Powers

variable (h : UnitaryFieldData ℓ f K) {n : ℕ}

@[expose] def twistedNorm (σ : K ≃+* K) (A : GL (Fin n) K) : ℕ → GL (Fin n) K
  | 0 => 1
  | k + 1 => twistedNorm σ A k * glAut (σ ^ k) A

theorem twistedNorm_zero (σ : K ≃+* K) (A : GL (Fin n) K) : twistedNorm σ A 0 = 1 := rfl

theorem twistedNorm_succ (σ : K ≃+* K) (A : GL (Fin n) K) (k : ℕ) :
    twistedNorm σ A (k + 1) = twistedNorm σ A k * glAut (σ ^ k) A := rfl

theorem twistedNorm_succ' (σ : K ≃+* K) (A : GL (Fin n) K) (k : ℕ) :
    twistedNorm σ A (k + 1) = A * glAut σ (twistedNorm σ A k) := by
  induction k with
  | zero => simp [twistedNorm]
  | succ k ih =>
    conv_rhs => rw [twistedNorm_succ]
    rw [twistedNorm_succ σ A (k + 1), ih, map_mul, ← MulAut.mul_apply, ← map_mul, ← pow_succ',
      mul_assoc]

theorem twistedNorm_mem (σ : K ≃+* K) {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (k : ℕ) :
    twistedNorm σ A k ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  induction k with
  | zero => exact Subgroup.one_mem _
  | succ k ih =>
    exact Subgroup.mul_mem _ ih (glAut_mem_primeFormUnitary h isPrimeFormGram_one _ hA)

theorem conj_mul_field_pow (σ : K ≃+* K)
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (k : ℕ) :
    (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A *
        primeFormFieldHom h isPrimeFormGram_one σ) ^ k =
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          ⟨twistedNorm σ (A : GL (Fin n) K) k, twistedNorm_mem h σ A.2 k⟩ *
        primeFormFieldHom h isPrimeFormGram_one (σ ^ k) := by
  induction k with
  | zero =>
    have h1 : (⟨twistedNorm σ (A : GL (Fin n) K) 0, twistedNorm_mem h σ A.2 0⟩ :
        primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := Subtype.ext rfl
    rw [pow_zero, pow_zero, h1, map_one, map_one, mul_one]
  | succ k ih =>
    have key := primeFormField_conj_eq h isPrimeFormGram_one (σ ^ k) A
    have key' : primeFormFieldHom h isPrimeFormGram_one (σ ^ k) *
        primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A =
        primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          (primeFormFieldU h isPrimeFormGram_one (σ ^ k) A) *
          primeFormFieldHom h isPrimeFormGram_one (σ ^ k) := by
      rw [← key, inv_mul_cancel_right]
    have hL : (⟨twistedNorm σ (A : GL (Fin n) K) (k + 1), twistedNorm_mem h σ A.2 (k + 1)⟩ :
        primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
        ⟨twistedNorm σ (A : GL (Fin n) K) k, twistedNorm_mem h σ A.2 k⟩ *
          primeFormFieldU h isPrimeFormGram_one (σ ^ k) A := Subtype.ext rfl
    rw [pow_succ, ih, hL, map_mul, pow_succ, map_mul (primeFormFieldHom h _)]
    calc _ = primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
            ⟨twistedNorm σ (A : GL (Fin n) K) k, twistedNorm_mem h σ A.2 k⟩ *
          (primeFormFieldHom h isPrimeFormGram_one (σ ^ k) *
            primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A) *
            primeFormFieldHom h isPrimeFormGram_one σ := by simp only [mul_assoc]
      _ = _ := by rw [key']; simp only [mul_assoc]

theorem glAut_scalar (σ : K ≃+* K) (c : Kˣ) :
    glAut σ (GeneralLinearGroup.scalar (Fin n) c) =
      GeneralLinearGroup.scalar (Fin n) (Units.map (σ : K →* K) c) := by
  ext i j
  rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, Matrix.map_apply,
    scalar_apply, scalar_apply, diagonal_apply, diagonal_apply]
  split_ifs <;> simp

theorem scalar_mul_comm (c : Kˣ) (g : GL (Fin n) K) :
    GeneralLinearGroup.scalar (Fin n) c * g = g * GeneralLinearGroup.scalar (Fin n) c := by
  ext i j
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, mul_comm]

theorem twistedNorm_scalar_mul (σ : K ≃+* K) (b : Kˣ) (A : GL (Fin n) K) (k : ℕ) :
    twistedNorm σ (GeneralLinearGroup.scalar (Fin n) b * A) k =
      GeneralLinearGroup.scalar (Fin n)
        (∏ i ∈ Finset.range k, Units.map ((σ ^ i : K ≃+* K) : K →* K) b) * twistedNorm σ A k := by
  induction k with
  | zero => simp [twistedNorm]
  | succ k ih =>
    rw [twistedNorm_succ, ih, map_mul, glAut_scalar, twistedNorm_succ, Finset.prod_range_succ,
      map_mul]
    rw [mul_assoc, ← mul_assoc (twistedNorm σ A k), ← scalar_mul_comm _ (twistedNorm σ A k)]
    simp only [mul_assoc]

end Powers

section Semilinear

variable {n : ℕ}

@[expose] def semilin (σ : K ≃+* K) (B : GL (Fin n) K) : (Fin n → K) ≃+ (Fin n → K) where
  toFun v := (B : Matrix (Fin n) (Fin n) K) *ᵥ fun i => σ (v i)
  invFun w := fun i => σ.symm ((((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) i)
  left_inv v := by
    funext i
    have e : (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        ((B : Matrix (Fin n) (Fin n) K) *ᵥ fun i => σ (v i))) = fun i => σ (v i) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    simp only [e, RingEquiv.symm_apply_apply]
  right_inv w := by
    have e : (fun j => σ (σ.symm ((((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) j))) =
        ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w :=
      funext fun j => RingEquiv.apply_symm_apply _ _
    change (B : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => σ (σ.symm
      ((((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) j))) = w
    rw [e, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  map_add' v w := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp

theorem semilin_apply (σ : K ≃+* K) (B : GL (Fin n) K) (v : Fin n → K) :
    semilin σ B v = (B : Matrix (Fin n) (Fin n) K) *ᵥ fun i => σ (v i) := rfl

theorem semilin_smul (σ : K ≃+* K) (B : GL (Fin n) K) (c : K) (v : Fin n → K) :
    semilin σ B (c • v) = σ c • semilin σ B v := by
  rw [semilin_apply, semilin_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem map_mulVec_ringEquiv (σ : K ≃+* K) (M : Matrix (Fin n) (Fin n) K) (w : Fin n → K) :
    (fun i => σ ((M *ᵥ w) i)) = M.map σ *ᵥ fun i => σ (w i) :=
  funext fun i => RingHom.map_mulVec (σ : K →+* K) M w i

theorem iterate_semilin (σ : K ≃+* K) (B : GL (Fin n) K) (k : ℕ) (v : Fin n → K) :
    (⇑(semilin σ B))^[k] v =
      (twistedNorm σ B k : Matrix (Fin n) (Fin n) K) *ᵥ fun i => (σ ^ k) (v i) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, twistedNorm_zero, Units.val_one, Matrix.one_mulVec]
    rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, semilin_apply, map_mulVec_ringEquiv,
      Matrix.mulVec_mulVec, twistedNorm_succ', Units.val_mul, coe_glAut]
    congr 1
    funext i
    rw [pow_succ']
    rfl

@[expose] def hform (h : UnitaryFieldData ℓ f K) (v w : Fin n → K) : K :=
  (fun i => h.bar (v i)) ⬝ᵥ w

theorem hform_mulVec (h : UnitaryFieldData ℓ f K) {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (x y : Fin n → K) :
    hform h ((A : Matrix (Fin n) (Fin n) K) *ᵥ x) ((A : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      hform h x y := by
  have hA' : ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1 := by
    have := (mem_primeFormUnitary).1 hA
    rwa [Units.val_one, Matrix.mul_one] at this
  have hb : (fun i => h.bar (((A : Matrix (Fin n) (Fin n) K) *ᵥ x) i)) =
      (A : Matrix (Fin n) (Fin n) K).map h.bar *ᵥ fun i => h.bar (x i) :=
    funext fun i => RingHom.map_mulVec h.bar _ x i
  rw [hform, hb, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, hA', Matrix.one_mulVec, dotProduct_comm, hform]

theorem hform_map (h : UnitaryFieldData ℓ f K) (σ : K ≃+* K) (v w : Fin n → K) :
    hform h (fun i => σ (v i)) (fun i => σ (w i)) = σ (hform h v w) := by
  simp only [hform, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow]

theorem bar_hform (h : UnitaryFieldData ℓ f K) (v w : Fin n → K) :
    h.bar (hform h v w) = hform h w v := by
  simp only [hform, dotProduct, map_sum, map_mul, UnitaryFieldData.bar_bar]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hform_semilin (h : UnitaryFieldData ℓ f K) (σ : K ≃+* K) {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (v w : Fin n → K) : hform h (semilin σ A v) (semilin σ A w) = σ (hform h v w) := by
  rw [semilin_apply, semilin_apply, hform_mulVec h hA, hform_map]

end Semilinear


open CFSG.LieType.Steinberg (exists_conjTr_mul_mul_eq_one)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (conjTr)

private theorem unitary_prime_semilinear_field_descent_core (h : UnitaryFieldData ℓ f K) {n : ℕ}
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (ha : orderOf a = p) (σ : K ≃+* K)
    (hσa : primeFormFieldFactor h isPrimeFormGram_one hn hq a = σ) (hσ : orderOf σ = p) :
    p ∣ f ∧ Nat.card (semilinearFixedSubfield σ) = (ℓ ^ (f / p)) ^ 2 ∧
      (∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ (f / p))) ∧
      (∀ x : K, h.norm x = 1 → σ (normσ σ p x) = normσ σ p x ∧
        normσ σ p x ^ (ℓ ^ (f / p) + 1) = 1) ∧
      (∀ y : K, σ y = y → y ^ (ℓ ^ (f / p) + 1) = 1 →
        ∃ x : K, h.norm x = 1 ∧ normσ σ p x = y) ∧
      ∃ M : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹ * a *
            primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M =
          primeFormFieldHom h isPrimeFormGram_one σ := by
  classical
  have : Finite K := h.finite
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨hpf, hcard, hbar⟩ := fixed_field_facts h hp hp2 σ hσ
  refine ⟨hpf, hcard, hbar, fun x hx => normσ_mem_normOne h hp hp2 σ hσ hx,
    fun y hy1 hy2 => exists_normσ_eq h hp hp2 σ hσ hy1 hy2, ?_⟩
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, hPsi, hker, -, -, hFapp, -, -, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨⟨A, σ'⟩, hA⟩ := hPsi a
  rw [primeFormPsi_apply] at hA
  have hσ' : σ' = σ := by rw [← hσa, ← hA, primeFormFieldFactor_apply]
  rw [hσ'] at hA
  have hLp : primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      ⟨twistedNorm σ (A : GL (Fin n) K) p, twistedNorm_mem h σ A.2 p⟩ = 1 := by
    have e := conj_mul_field_pow h σ A p
    rw [hA, show a ^ p = 1 from ha ▸ pow_orderOf_eq_one a, hσp, map_one, mul_one] at e
    exact e.symm
  obtain ⟨-, c, hc1, hcL⟩ := (hker ⟨⟨twistedNorm σ (A : GL (Fin n) K) p,
    twistedNorm_mem h σ A.2 p⟩, 1⟩).1 (by rw [primeFormPsi_apply, map_one, mul_one, hLp])
  change twistedNorm σ (A : GL (Fin n) K) p = GeneralLinearGroup.scalar (Fin n) c at hcL
  have hσc : σ (c : K) = c := by
    have e1 := twistedNorm_succ σ (A : GL (Fin n) K) p
    have e2 := twistedNorm_succ' σ (A : GL (Fin n) K) p
    rw [hσp, map_one, MulAut.one_apply, hcL] at e1
    rw [hcL, glAut_scalar] at e2
    have e3 : GeneralLinearGroup.scalar (Fin n) c * (A : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) (Units.map (σ : K →* K) c) * A := by
      rw [← e1, e2, scalar_mul_comm]
    have e4 := mul_right_cancel e3
    have e5 := congrArg (fun g : GL (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) e4
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.coe_map] at e5
    exact e5.symm
  have hcq : (c : K) ^ (ℓ ^ (f / p) + 1) = 1 := by
    rw [pow_succ', ← hbar _ hσc]
    exact hc1
  obtain ⟨b, hb1, hb⟩ := exists_normσ_eq h hp hp2 σ hσ (y := (c : K)⁻¹)
    (by rw [map_inv₀, hσc]) (by rw [inv_pow, hcq, inv_one])
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [UnitaryFieldData.norm, zero_mul] at hb1
    exact zero_ne_one hb1
  have hS : GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0) ∈
      primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    scalar_mem_primeFormUnitary_one h hb1
  have hcS : primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨_, hS⟩ = 1 := by
    have := (hker ⟨⟨_, hS⟩, 1⟩).2 ⟨rfl, Units.mk0 b hb0, hb1, rfl⟩
    rwa [primeFormPsi_apply, map_one, mul_one] at this
  obtain ⟨A', hA'⟩ : ∃ A' : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      A' = ⟨_, hS⟩ * A := ⟨_, rfl⟩
  have hcA' : primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A' =
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A := by
    rw [hA', map_mul, hcS, one_mul]
  have hA'g : (A' : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0) * A := by
    rw [hA']
    rfl
  have hL' : twistedNorm σ (A' : GL (Fin n) K) p = 1 := by
    rw [hA'g, twistedNorm_scalar_mul, hcL, ← map_mul]
    rw [← map_one (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K)]
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.coe_prod]
    simp only [Units.coe_map, Units.val_mk0, Units.val_one]
    change normσ σ p b * c = 1
    rw [hb, inv_mul_cancel₀ c.ne_zero]
  set γ := semilin σ (A' : GL (Fin n) K) with hγ
  have hγp : ∀ v, (⇑γ)^[p] v = v := fun v => by
    rw [hγ, iterate_semilin, hL', Units.val_one, Matrix.one_mulVec, hσp]
    rfl
  have h2f : 1 ≤ 2 * f := by have := h.one_le; omega
  obtain ⟨-, -, -, -, bb, hbb, -⟩ := CFSG.RankThree.Classical.semilinear_fixed_basis h.prime h2f
    h.card σ hσ (Module.finrank_fin_fun K) γ (semilin_smul σ _) hγp
  have hfix : ∀ i j, σ (hform h (bb i) (bb j)) = hform h (bb i) (bb j) := fun i j => by
    have := hform_semilin h σ A'.2 (bb i) (bb j)
    rw [← hγ, hbb, hbb] at this
    exact this.symm
  set K₀ := semilinearFixedSubfield σ with hK₀
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : Finite K₀ := Subtype.finite
  have := Fintype.ofFinite K₀
  have : CharP K₀ ℓ := charP_of_card_eq_prime_pow (f := 2 * (f / p)) (by
    rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
  set G₀ : Matrix (Fin n) (Fin n) K₀ :=
    Matrix.of fun i j => ⟨hform h (bb i) (bb j), RingHom.mem_eqLocusField.mpr (hfix i j)⟩ with hG₀
  have hσ₀ : ∀ x : K₀, ((unitaryInvolution K₀ ℓ (f / p) x : K₀) : K) = h.bar x := fun x => by
    rw [unitaryInvolution_apply, SubmonoidClass.coe_pow, hbar _ (RingHom.mem_eqLocusField.mp x.2)]
  have hGh : conjTr (unitaryInvolution K₀ ℓ (f / p)) G₀ = G₀ := by
    ext i j
    rw [conjTr, Matrix.transpose_apply, Matrix.map_apply, hσ₀]
    simp only [hG₀, Matrix.of_apply]
    exact bar_hform h _ _
  set Bm : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => bb j i with hBm
  have hBmT : Bm = (Pi.basisFun K (Fin n)).toMatrix bb := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rfl
  have hBm_inv : Bm * bb.toMatrix (Pi.basisFun K (Fin n)) = 1 := by
    rw [hBmT, Module.Basis.toMatrix_mul_toMatrix_flip]
  have hdetB : Bm.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hBm_inv
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hGB : G₀.map K₀.subtype = (Bm.map h.bar)ᵀ * Bm := by
    ext i j
    simp only [hG₀, hBm, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      Matrix.transpose_apply, hform, dotProduct]
    rfl
  have hdet₀ : G₀.det ≠ 0 := by
    intro h0
    have e1 : ((G₀.det : K₀) : K) = (G₀.map K₀.subtype).det := RingHom.map_det K₀.subtype G₀
    have e2 : h.bar Bm.det = (Bm.map h.bar).det := RingHom.map_det h.bar Bm
    rw [h0, ZeroMemClass.coe_zero, hGB, Matrix.det_mul, Matrix.det_transpose, ← e2] at e1
    exact mul_ne_zero ((map_ne_zero h.bar).mpr hdetB) hdetB e1.symm
  obtain ⟨P, hP⟩ := exists_conjTr_mul_mul_eq_one (p := ℓ) (f := f / p) hcard hGh hdet₀
  set PK : Matrix (Fin n) (Fin n) K := (P : Matrix (Fin n) (Fin n) K₀).map K₀.subtype with hPK
  set Mm : Matrix (Fin n) (Fin n) K := Bm * PK with hMm
  have hPKbar : PK.map h.bar = ((P : Matrix (Fin n) (Fin n) K₀).map
      (unitaryInvolution K₀ ℓ (f / p))).map K₀.subtype := by
    ext i j
    simp only [hPK, Matrix.map_apply]
    exact (hσ₀ _).symm
  have hMU : (Mm.map h.bar)ᵀ * Mm = 1 := by
    have e := congrArg (fun X => X.map K₀.subtype) hP
    simp only [conjTr, Matrix.map_mul, Matrix.transpose_map, Matrix.map_one _ (map_zero _)
      (map_one _)] at e
    rw [hMm, Matrix.map_mul, Matrix.transpose_mul, hPKbar, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Bm.map h.bar)ᵀ, ← hGB, ← Matrix.mul_assoc, hPK]
    exact e
  set Mg : GL (Fin n) K := ⟨Mm, (Mm.map h.bar)ᵀ, mul_eq_one_comm.mp hMU, hMU⟩ with hMg
  have hMgU : Mg ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
    exact hMU
  have hcol : ∀ j, (fun i => Mm i j) = ∑ k, ((P k j : K₀) : K) • bb k := fun j => by
    funext i
    simp only [hMm, hBm, hPK, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hγcol : ∀ j, γ (fun i => Mm i j) = fun i => Mm i j := fun j => by
    rw [hcol, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hPkj : σ ((P k j : K₀) : K) = (P k j : K₀) := RingHom.mem_eqLocusField.mp (P k j).2
    rw [hγ, semilin_smul, ← hγ, hbb, hPkj]
  have hfixM : (A' : GL (Fin n) K) * glAut σ Mg = Mg := by
    apply Units.ext
    rw [Units.val_mul, coe_glAut]
    ext i j
    have := congrFun (hγcol j) i
    rw [hγ, semilin_apply] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hMg] using this
  refine ⟨⟨Mg, hMgU⟩, ?_⟩
  have key := primeFormField_conj_eq h isPrimeFormGram_one σ ⟨Mg, hMgU⟩
  have key' : primeFormFieldHom h isPrimeFormGram_one σ *
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨Mg, hMgU⟩ =
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        (primeFormFieldU h isPrimeFormGram_one σ ⟨Mg, hMgU⟩) *
        primeFormFieldHom h isPrimeFormGram_one σ := by
    rw [← key, inv_mul_cancel_right]
  have hU1 : (⟨Mg, hMgU⟩ : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹ *
      (A' * primeFormFieldU h isPrimeFormGram_one σ ⟨Mg, hMgU⟩) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU, hfixM,
      inv_mul_cancel, Subgroup.coe_one]
  rw [← hA, ← hcA', mul_assoc, mul_assoc, key', ← mul_assoc, ← mul_assoc, ← map_inv,
    ← map_mul, ← map_mul, mul_assoc, hU1, map_one, one_mul]

theorem unitary_prime_semilinear_field_descent (h : UnitaryFieldData ℓ f K) {n : ℕ}
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (_hpℓ : p ≠ ℓ)
    (a : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (ha : orderOf a = p) (σ : K ≃+* K)
    (hσa : primeFormFieldFactor h isPrimeFormGram_one hn hq a = σ) (hσ : orderOf σ = p) :
    p ∣ f ∧ Nat.card (semilinearFixedSubfield σ) = (ℓ ^ (f / p)) ^ 2 ∧
      (∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ (f / p))) ∧
      (∀ x : K, h.norm x = 1 → σ (normσ σ p x) = normσ σ p x ∧
        normσ σ p x ^ (ℓ ^ (f / p) + 1) = 1) ∧
      (∀ y : K, σ y = y → y ^ (ℓ ^ (f / p) + 1) = 1 →
        ∃ x : K, h.norm x = 1 ∧ normσ σ p x = y) ∧
      ∃ M : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹ * a *
            primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M =
          primeFormFieldHom h isPrimeFormGram_one σ :=
  unitary_prime_semilinear_field_descent_core h hn hq hp hp2 a ha σ hσa hσ

end CFSG.RankThree.UnitaryDescent
