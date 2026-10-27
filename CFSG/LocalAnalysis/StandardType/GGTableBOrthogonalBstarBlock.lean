module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace TableBOrth

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

section Block

@[expose] def blk (a b : ι) (x : Matrix ι ι K) : Matrix (Fin 2) (Fin 2) K :=
  x.submatrix ![a, b] ![a, b]

omit [DecidableEq ι] in
theorem blk_mul {a b : ι} (hab : a ≠ b) {x : Matrix ι ι K}
    (hx : ∀ j, j ≠ a → j ≠ b → x a j = 0 ∧ x b j = 0) (y : Matrix ι ι K) :
    blk a b (x * y) = blk a b x * blk a b y := by
  ext r s
  simp only [blk, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_two]
  rw [Finset.sum_eq_add a b hab]
  · fin_cases r <;> fin_cases s <;> simp
  · intro c _ hc
    fin_cases r <;> simp [(hx c hc.1 hc.2).1, (hx c hc.1 hc.2).2]
  · simp
  · simp

omit [Fintype ι] in
theorem blk_one (a b : ι) (hab : a ≠ b) : blk a b (1 : Matrix ι ι K) = 1 := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp [blk, Matrix.one_apply, hab, Ne.symm hab]

theorem blk_pow {a b : ι} (hab : a ≠ b) {x : Matrix ι ι K}
    (hx : ∀ j, j ≠ a → j ≠ b → x a j = 0 ∧ x b j = 0) (n : ℕ) :
    blk a b (x ^ n) = blk a b x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, blk_one a b hab]
  | succ n ih => rw [pow_succ', blk_mul hab hx, ih, pow_succ']

variable [CharP K 2]

theorem trace_det_of_pow_two_pow {B : Matrix (Fin 2) (Fin 2) K} {n : ℕ} (h : B ^ (2 ^ n) = 1) :
    B.trace = 0 ∧ B.det = 1 := by
  constructor
  · have h1 : (B - 1) ^ (2 ^ n) = 0 := by
      rw [sub_pow_char_pow_of_commute (p := 2) (h := Commute.one_right B), h, one_pow, sub_self]
    have h2 := Matrix.isNilpotent_trace_of_isNilpotent ⟨_, h1⟩
    have h3 : (B - 1).trace = 0 := h2.eq_zero
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, sub_eq_zero] at h3
    rw [h3]
    exact CharTwo.two_eq_zero (R := K) ▸ (by norm_num)
  · have h1 : B.det ^ (2 ^ n) = 1 := by rw [← Matrix.det_pow, h, Matrix.det_one]
    have h2 : (B.det - 1) ^ (2 ^ n) = 0 := by rw [sub_pow_char_pow, h1, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h2)

end Block

section Levi

open SeitzReduction.OmegaPilot

omit [DecidableEq ι] in
theorem mul_apply_of_row {x y : Matrix ι ι K} {a b : ι} (hab : a ≠ b) {i : ι}
    (hx : ∀ j, j ≠ a → j ≠ b → x i j = 0) (k : ι) :
    (x * y) i k = x i a * y a k + x i b * y b k := by
  rw [Matrix.mul_apply, Finset.sum_eq_add a b hab]
  · intro c _ hc
    rw [hx c hc.1 hc.2, zero_mul]
  · simp
  · simp

theorem polar_mulVec_of_mem_orthGroup {QF : QuadraticForm K (ι → K)} {x : GL ι K}
    (hx : x ∈ LargeEvenOrthGroup ⇑QF) (v w : ι → K) :
    QuadraticMap.polar QF ((x : Matrix ι ι K) *ᵥ v) ((x : Matrix ι ι K) *ᵥ w) =
      QuadraticMap.polar QF v w := by
  simp only [QuadraticMap.polar, ← Matrix.mulVec_add, isometry_of_mem_orthGroup hx]

theorem mulVec_single_eq_of_col {x : Matrix ι ι K} {j : ι}
    (h : ∀ i, x i j = (1 : Matrix ι ι K) i j) : x *ᵥ Pi.single j 1 = Pi.single j 1 := by
  rw [Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply, h, Matrix.one_apply, Pi.single_apply]

variable [CharP K 2]

theorem fix_or_fix_of_pGroup {QF : QuadraticForm K (ι → K)} {a0 b0 a1 b1 : ι}
    (h0 : IsHypCoord QF a0 b0) (h1 : IsHypCoord QF a1 b1) (ha01 : a0 ≠ a1) (hab : a0 ≠ b1)
    (hba : b0 ≠ a1) (hbb : b0 ≠ b1) {ζ : Kˣ} (hζ2 : ζ * ζ ≠ 1) {δ₀ : ι → Kˣ}
    (hδa : δ₀ a0 = ζ) (hδb : δ₀ b1 = 1) {P : Subgroup (GL ι K)}
    (hPO : P ≤ LargeEvenOrthGroup ⇑QF) (hP2 : IsPGroup 2 P)
    (hrow : ∀ x ∈ P, ∀ j, j ≠ a0 → j ≠ b1 →
      (x : Matrix ι ι K) a0 j = 0 ∧ (x : Matrix ι ι K) b1 j = 0)
    (hcolW : ∀ x ∈ P, ∀ i, i ≠ a0 → i ≠ b1 →
      (x : Matrix ι ι K) i a0 = 0 ∧ (x : Matrix ι ι K) i b1 = 0)
    (hcolW' : ∀ x ∈ P, ∀ i, i ≠ b0 → i ≠ a1 →
      (x : Matrix ι ι K) i b0 = 0 ∧ (x : Matrix ι ι K) i a1 = 0)
    (hnorm : ∀ x ∈ P, TauCeti.diagGL δ₀ * x * (TauCeti.diagGL δ₀)⁻¹ ∈ P)
    (hrest : ∀ x ∈ P, ∀ i, i ≠ a0 → i ≠ b0 → i ≠ a1 → i ≠ b1 →
      ∀ i', (x : Matrix ι ι K) i' i = (1 : Matrix ι ι K) i' i) :
    (∀ x ∈ P, ∀ i, i ≠ b0 → i ≠ b1 → ∀ i', (x : Matrix ι ι K) i' i = (1 : Matrix ι ι K) i' i) ∨
      (∀ x ∈ P, ∀ i, i ≠ a0 → i ≠ a1 →
        ∀ i', (x : Matrix ι ι K) i' i = (1 : Matrix ι ι K) i' i) := by
  have hunip : ∀ x ∈ P, (x : Matrix ι ι K) a0 a0 + (x : Matrix ι ι K) b1 b1 = 0 ∧
      (x : Matrix ι ι K) a0 a0 * (x : Matrix ι ι K) b1 b1 -
        (x : Matrix ι ι K) a0 b1 * (x : Matrix ι ι K) b1 a0 = 1 := by
    intro x hx
    obtain ⟨n, hn⟩ := hP2 ⟨x, hx⟩
    have hxn : (x : Matrix ι ι K) ^ (2 ^ n) = 1 := by
      have := congrArg (fun y : P => ((y : GL ι K) : Matrix ι ι K)) hn
      simpa using this
    have hB := blk_pow hab (hrow x hx) (2 ^ n)
    rw [hxn, blk_one a0 b1 hab] at hB
    obtain ⟨ht, hd⟩ := trace_det_of_pow_two_pow hB.symm
    rw [Matrix.trace_fin_two] at ht
    rw [Matrix.det_fin_two] at hd
    exact ⟨by simpa [blk] using ht, by simpa [blk] using hd⟩
  have hconj : ∀ x : GL ι K, ∀ i j, ((TauCeti.diagGL δ₀ * x * (TauCeti.diagGL δ₀)⁻¹ : GL ι K) :
      Matrix ι ι K) i j = (δ₀ i : K) * (x : Matrix ι ι K) i j * ((δ₀ j)⁻¹ : Kˣ) := by
    intro x i j
    rw [← map_inv, Units.val_mul, Units.val_mul, TauCeti.diagGL_coe, TauCeti.diagGL_coe,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  have hζK : (ζ : K) + ((ζ⁻¹ : Kˣ) : K) ≠ 0 := by
    intro h
    apply hζ2
    apply Units.ext
    have h' : (ζ : K) = ((ζ⁻¹ : Kˣ) : K) := by
      rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
      exact h
    rw [Units.val_mul, Units.val_one]
    nth_rewrite 2 [h']
    exact Units.mul_inv ζ
  have htri : ∀ x ∈ P, (x : Matrix ι ι K) a0 a0 = 1 ∧ (x : Matrix ι ι K) b1 b1 = 1 ∧
      (x : Matrix ι ι K) a0 b1 * (x : Matrix ι ι K) b1 a0 = 0 := by
    intro x hx
    set y := TauCeti.diagGL δ₀ * x * (TauCeti.diagGL δ₀)⁻¹ with hy
    have hxy := hunip (x * y) (P.mul_mem hx (hnorm x hx))
    rw [Units.val_mul] at hxy
    have e1 := mul_apply_of_row (y := (y : Matrix ι ι K)) hab
      (fun j h1 h2 => (hrow x hx j h1 h2).1) a0
    have e2 := mul_apply_of_row (y := (y : Matrix ι ι K)) hab
      (fun j h1 h2 => (hrow x hx j h1 h2).2) b1
    rw [hy, hconj, hconj, hδa, hδb] at e1 e2
    obtain ⟨hx1, hx2⟩ := hunip x hx
    set α := (x : Matrix ι ι K) a0 a0
    set β := (x : Matrix ι ι K) a0 b1
    set γ := (x : Matrix ι ι K) b1 a0
    set δ := (x : Matrix ι ι K) b1 b1
    have hαδ : δ = α := by
      have : α + δ = 0 := hx1
      rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq, add_comm]
      exact this
    have hz : (ζ : K) * ((ζ⁻¹ : Kˣ) : K) = 1 := Units.mul_inv ζ
    have hbg : β * γ * ((ζ : K) + ((ζ⁻¹ : Kˣ) : K)) = 0 := by
      have h3 := hxy.1
      rw [e1, e2] at h3
      simp only [Units.val_one, inv_one, mul_one, one_mul] at h3
      rw [hαδ] at h3
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h3 - α ^ 2 * hz - α ^ 2 * h2
    have hbg0 : β * γ = 0 := (mul_eq_zero.mp hbg).resolve_right hζK
    have hα1 : α = 1 := by
      have h4 : α * α = 1 := by
        rw [hαδ] at hx2
        linear_combination hx2 + hbg0
      have h5 : (α - 1) ^ 2 = 0 := by
        have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
        linear_combination h4 + (1 - α) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h5)
    exact ⟨hα1, hαδ ▸ hα1, hbg0⟩
  have hdich : (∀ x ∈ P, (x : Matrix ι ι K) b1 a0 = 0) ∨
      (∀ x ∈ P, (x : Matrix ι ι K) a0 b1 = 0) := by
    by_contra h
    push Not at h
    obtain ⟨⟨x, hx, hxγ⟩, ⟨y, hy, hyβ⟩⟩ := h
    have hxβ : (x : Matrix ι ι K) a0 b1 = 0 := (mul_eq_zero.mp (htri x hx).2.2).resolve_right hxγ
    have hyγ : (y : Matrix ι ι K) b1 a0 = 0 := (mul_eq_zero.mp (htri y hy).2.2).resolve_left hyβ
    have hyx := hunip (y * x) (P.mul_mem hy hx)
    rw [Units.val_mul] at hyx
    have e1 := mul_apply_of_row (y := (x : Matrix ι ι K)) hab
      (fun j h1 h2 => (hrow y hy j h1 h2).1) a0
    have e2 := mul_apply_of_row (y := (x : Matrix ι ι K)) hab
      (fun j h1 h2 => (hrow y hy j h1 h2).2) b1
    have h3 := hyx.1
    rw [e1, e2, (htri x hx).1, (htri x hx).2.1, (htri y hy).1, (htri y hy).2.1, hxβ, hyγ] at h3
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h4 : (y : Matrix ι ι K) a0 b1 * (x : Matrix ι ι K) b1 a0 = 0 := by
      linear_combination h3 - h2
    exact (mul_eq_zero.mp h4).elim hyβ hxγ
  rcases hdich with hA | hB
  · left
    intro x hx
    have hca0 : ∀ i', (x : Matrix ι ι K) i' a0 = (1 : Matrix ι ι K) i' a0 := by
      intro i'
      by_cases h1 : i' = a0
      · subst h1
        rw [Matrix.one_apply_eq]
        exact (htri x hx).1
      · rw [Matrix.one_apply_ne h1]
        by_cases h2 : i' = b1
        · subst h2
          exact hA x hx
        · exact (hcolW x hx i' h1 h2).1
    have hxa0 : (x : Matrix ι ι K) *ᵥ Pi.single a0 1 = Pi.single a0 1 :=
      mulVec_single_eq_of_col hca0
    have hxb1 : (x : Matrix ι ι K) *ᵥ Pi.single b1 1 =
        (x : Matrix ι ι K) a0 b1 • Pi.single a0 1 + Pi.single b1 1 := by
      rw [Matrix.mulVec_single_one]
      funext i
      simp only [Matrix.col_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      by_cases hi1 : i = a0
      · rw [hi1]
        simp [hab]
      · by_cases hi2 : i = b1
        · rw [hi2]
          simp [hab.symm, (htri x hx).2.1]
        · simp [hi1, hi2, (hcolW x hx i hi1 hi2).2]
    have hO := hPO hx
    have hb0a1 : (x : Matrix ι ι K) b0 a1 = 0 := by
      have h3 := polar_mulVec_of_mem_orthGroup hO (Pi.single a0 1) (Pi.single a1 1)
      rw [hxa0, h0.polar_left, h0.polar_left, Matrix.mulVec_single_one, Matrix.col_apply,
        Pi.single_eq_of_ne hba] at h3
      exact h3
    have ha1a1 : (x : Matrix ι ι K) a1 a1 = 1 := by
      have h3 := polar_mulVec_of_mem_orthGroup hO (Pi.single b1 1) (Pi.single a1 1)
      rw [hxb1, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, h0.polar_left,
        h1.polar_right, h1.polar_right, Matrix.mulVec_single_one, Matrix.col_apply,
        Matrix.col_apply, hb0a1, smul_zero, zero_add, Pi.single_eq_same] at h3
      exact h3
    intro i hib0 hib1 i'
    by_cases h1 : i = a0
    · subst h1
      exact hca0 i'
    · by_cases h2 : i = a1
      · subst h2
        by_cases h3 : i' = i
        · subst h3
          rw [Matrix.one_apply_eq]
          exact ha1a1
        · rw [Matrix.one_apply_ne h3]
          by_cases h4 : i' = b0
          · subst h4
            exact hb0a1
          · exact (hcolW' x hx i' h4 h3).2
      · exact hrest x hx i h1 hib0 h2 hib1 i'
  · right
    intro x hx
    have hcb1 : ∀ i', (x : Matrix ι ι K) i' b1 = (1 : Matrix ι ι K) i' b1 := by
      intro i'
      by_cases h1 : i' = b1
      · subst h1
        rw [Matrix.one_apply_eq]
        exact (htri x hx).2.1
      · rw [Matrix.one_apply_ne h1]
        by_cases h2 : i' = a0
        · subst h2
          exact hB x hx
        · exact (hcolW x hx i' h2 h1).2
    have hxb1 : (x : Matrix ι ι K) *ᵥ Pi.single b1 1 = Pi.single b1 1 :=
      mulVec_single_eq_of_col hcb1
    have hxa0 : (x : Matrix ι ι K) *ᵥ Pi.single a0 1 =
        Pi.single a0 1 + (x : Matrix ι ι K) b1 a0 • Pi.single b1 1 := by
      rw [Matrix.mulVec_single_one]
      funext i
      simp only [Matrix.col_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      by_cases hi1 : i = a0
      · rw [hi1]
        simp [hab, (htri x hx).1]
      · by_cases hi2 : i = b1
        · rw [hi2]
          simp [hab.symm]
        · simp [hi1, hi2, (hcolW x hx i hi1 hi2).1]
    have hO := hPO hx
    have ha1b0 : (x : Matrix ι ι K) a1 b0 = 0 := by
      have h3 := polar_mulVec_of_mem_orthGroup hO (Pi.single b1 1) (Pi.single b0 1)
      rw [hxb1, h1.polar_right, h1.polar_right, Matrix.mulVec_single_one, Matrix.col_apply,
        Pi.single_eq_of_ne hba.symm] at h3
      exact h3
    have hb0b0 : (x : Matrix ι ι K) b0 b0 = 1 := by
      have h3 := polar_mulVec_of_mem_orthGroup hO (Pi.single a0 1) (Pi.single b0 1)
      rw [hxa0, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, h0.polar_left,
        h1.polar_right, h0.polar_left, Matrix.mulVec_single_one, Matrix.col_apply,
        Matrix.col_apply, ha1b0, smul_zero, add_zero, Pi.single_eq_same] at h3
      exact h3
    intro i hia0 hia1 i'
    by_cases h1 : i = b1
    · subst h1
      exact hcb1 i'
    · by_cases h2 : i = b0
      · subst h2
        by_cases h3 : i' = i
        · subst h3
          rw [Matrix.one_apply_eq]
          exact hb0b0
        · rw [Matrix.one_apply_ne h3]
          by_cases h4 : i' = a1
          · subst h4
            exact ha1b0
          · exact (hcolW' x hx i' h3 h4).1
      · exact hrest x hx i hia0 h2 hia1 h1 i'

end Levi

end TableBOrth

end CFSG.StandardType
