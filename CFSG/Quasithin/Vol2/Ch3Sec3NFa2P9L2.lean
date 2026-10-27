module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2L2Gen
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2PslConj

public section

namespace CFSG.Quasithin.H13.NFa2

open scoped MatrixGroups

abbrev p9Rot {F : Type*} [CommRing F] (a b : F) : Matrix (Fin 2) (Fin 2) F := !![a, -b; b, a]

lemma p9Rot_mul {F : Type*} [CommRing F] (a b c d : F) :
    p9Rot a b * p9Rot c d = p9Rot (a * c - b * d) (a * d + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma p9Rot_one {F : Type*} [CommRing F] : p9Rot (1 : F) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma p9Rot_zero_eq_scalar {F : Type*} [CommRing F] (a : F) :
    p9Rot a 0 = Matrix.scalar (Fin 2) a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply]

lemma p9Rot_neg {F : Type*} [CommRing F] (a b : F) : -p9Rot a b = p9Rot (-a) (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma p9_scalar_one {F : Type*} [CommRing F] : Matrix.scalar (Fin 2) (1 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply]

lemma p9_scalar_neg_one {F : Type*} [CommRing F] : Matrix.scalar (Fin 2) (-1 : F) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply]

lemma p9S_mul_self {F : Type*} [CommRing F] :
    (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def p9S0 (F : Type*) [CommRing F] : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

lemma p9_S0_coe {F : Type*} [CommRing F] :
    ((p9S0 F : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, -1; 1, 0] := rfl

lemma p9_S0_sq {F : Type*} [CommRing F] : p9S0 F ^ 2 = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, sq, p9_S0_coe, p9S_mul_self]

lemma p9_mk_eq_one_iff {F : Type*} [Field F] (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    (QuotientGroup.mk A : PSL(2, F)) = 1 ↔
      ∃ r : F, r ^ 2 = 1 ∧ Matrix.scalar (Fin 2) r = (A : Matrix (Fin 2) (Fin 2) F) := by
  have h := QuotientGroup.eq_one_iff (N := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) A
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at h
  exact h.trans ⟨fun ⟨r, hr, h⟩ => ⟨r, by simpa using hr, h⟩,
    fun ⟨r, hr, h⟩ => ⟨r, by simpa using hr, h⟩⟩

lemma p9_mk_neg_one {F : Type*} [Field F] :
    (QuotientGroup.mk (-1 : Matrix.SpecialLinearGroup (Fin 2) F) : PSL(2, F)) = 1 := by
  rw [p9_mk_eq_one_iff]
  refine ⟨-1, by norm_num, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, p9_scalar_neg_one]

lemma p9_orderOf_c0 {F : Type*} [Field F] :
    orderOf (QuotientGroup.mk (p9S0 F) : PSL(2, F)) = 2 := by
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, p9_S0_sq, p9_mk_neg_one]
  · rw [Ne, p9_mk_eq_one_iff]
    rintro ⟨r, -, h⟩
    have h01 := congrFun (congrFun h 0) 1
    rw [p9_S0_coe] at h01
    norm_num [Matrix.scalar_apply, Matrix.diagonal_apply] at h01

lemma p9_form_comm {F : Type*} [CommRing F] (B : Matrix (Fin 2) (Fin 2) F)
    (hB : B.det = 1) (hc : B * !![0, -1; 1, 0] = !![0, -1; 1, 0] * B) :
    B = p9Rot (B 0 0) (-B 0 1) ∧ B 0 0 ^ 2 + (-B 0 1) ^ 2 = 1 := by
  have h11 : B 1 1 = B 0 0 := by
    have h := congrFun (congrFun hc 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h
    first | linear_combination h | linear_combination -h
  have h10 : B 1 0 = -B 0 1 := by
    have h := congrFun (congrFun hc 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h
    first | linear_combination h | linear_combination -h
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [p9Rot, h11, h10]
  · rw [Matrix.det_fin_two, h11, h10] at hB
    linear_combination hB

lemma p9_form_anticomm {F : Type*} [CommRing F] (B : Matrix (Fin 2) (Fin 2) F)
    (hB : B.det = 1) (hc : B * !![0, -1; 1, 0] = -(!![0, -1; 1, 0] * B)) : B * B = -1 := by
  have hr : B 1 0 = B 0 1 := by
    have h := congrFun (congrFun hc 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h
    first | linear_combination h | linear_combination -h
  have hs : B 1 1 = -B 0 0 := by
    have h := congrFun (congrFun hc 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h
    first | linear_combination h | linear_combination -h
  rw [Matrix.det_fin_two, hs, hr] at hB
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hr, hs] <;>
    first | ring1 | linear_combination -hB

lemma p9_mk_sq_eq_one_of_anticomm {F : Type*} [Field F] (B : Matrix.SpecialLinearGroup (Fin 2) F)
    (hc : (B : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] =
      -(!![0, -1; 1, 0] * (B : Matrix (Fin 2) (Fin 2) F))) :
    (QuotientGroup.mk B : PSL(2, F)) ^ 2 = 1 := by
  rw [← QuotientGroup.mk_pow]
  have hB2 : B ^ 2 = -1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, sq]
    exact p9_form_anticomm _ B.2 hc
  rw [hB2, p9_mk_neg_one]

lemma p9_comm_dichotomy {F : Type*} [Field F] (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (h : (QuotientGroup.mk A : PSL(2, F)) * QuotientGroup.mk (p9S0 F) =
      QuotientGroup.mk (p9S0 F) * QuotientGroup.mk A) :
    (A : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] =
        !![0, -1; 1, 0] * (A : Matrix (Fin 2) (Fin 2) F) ∨
      (A : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] =
        -(!![0, -1; 1, 0] * (A : Matrix (Fin 2) (Fin 2) F)) := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h
  have h' := (QuotientGroup.eq (a := A * p9S0 F) (b := p9S0 F * A)).mp h
  obtain ⟨r, hr, hz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h'
  have key : p9S0 F * A = (A * p9S0 F) * ((A * p9S0 F)⁻¹ * (p9S0 F * A)) :=
    (mul_inv_cancel_left _ _).symm
  set z := (A * p9S0 F)⁻¹ * (p9S0 F * A) with hzdef
  have hm := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F =>
    (X : Matrix (Fin 2) (Fin 2) F)) key
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [← hz, p9_S0_coe] at hm
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hr' : (r - 1) * (r + 1) = 0 := by linear_combination hr2
  rcases mul_eq_zero.mp hr' with h1 | h1
  · obtain rfl : r = 1 := by linear_combination h1
    rw [p9_scalar_one, mul_one] at hm
    exact Or.inl hm.symm
  · obtain rfl : r = -1 := by linear_combination h1
    rw [p9_scalar_neg_one, mul_neg, mul_one] at hm
    exact Or.inr (by rw [hm, neg_neg])

lemma p9_order_three_of_rot {F : Type*} [Field F] (B : Matrix.SpecialLinearGroup (Fin 2) F)
    (a b : F) (hB : (B : Matrix (Fin 2) (Fin 2) F) = p9Rot a b) (hab : a ^ 2 + b ^ 2 = 1)
    (h3 : orderOf (QuotientGroup.mk B : PSL(2, F)) = 3) : 4 * a ^ 2 = 1 := by
  have hb : b ≠ 0 := by
    rintro rfl
    have h1 : (QuotientGroup.mk B : PSL(2, F)) = 1 := by
      rw [p9_mk_eq_one_iff]
      refine ⟨a, by linear_combination hab, ?_⟩
      rw [hB, p9Rot_zero_eq_scalar]
    rw [h1, orderOf_one] at h3
    norm_num at h3
  have hcube : (QuotientGroup.mk B : PSL(2, F)) ^ 3 = 1 := by
    rw [← h3]; exact pow_orderOf_eq_one _
  rw [← QuotientGroup.mk_pow, p9_mk_eq_one_iff] at hcube
  obtain ⟨r, -, hr⟩ := hcube
  have hpow : (p9Rot a b ^ 3) 1 0 = b * (3 * a ^ 2 - b ^ 2) := by
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hs0 : (Matrix.scalar (Fin 2) r) 1 0 = 0 := by
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  have e10 := congrFun (congrFun hr 1) 0
  rw [Matrix.SpecialLinearGroup.coe_pow, hB, hpow, hs0] at e10
  have h2 : b * (4 * a ^ 2 - 1) = 0 := by linear_combination (-1 : F) * e10 + b * hab
  have h4 : 4 * a ^ 2 - 1 = 0 := (mul_eq_zero.mp h2).resolve_left hb
  linear_combination h4

lemma p9_mk_mem_zpowers_of_rot {F : Type*} [Field F] (B₁ B₂ : Matrix.SpecialLinearGroup (Fin 2) F)
    (a₁ b₁ a₂ b₂ : F) (h4 : (4 : F) ≠ 0)
    (h₁ : (B₁ : Matrix (Fin 2) (Fin 2) F) = p9Rot a₁ b₁)
    (h₂ : (B₂ : Matrix (Fin 2) (Fin 2) F) = p9Rot a₂ b₂)
    (hab₁ : a₁ ^ 2 + b₁ ^ 2 = 1) (hab₂ : a₂ ^ 2 + b₂ ^ 2 = 1)
    (ha₁ : 4 * a₁ ^ 2 = 1) (ha₂ : 4 * a₂ ^ 2 = 1) :
    (QuotientGroup.mk B₂ : PSL(2, F)) ∈ Subgroup.zpowers (QuotientGroup.mk B₁) := by
  have hsa : a₂ ^ 2 = a₁ ^ 2 := by
    have h : (4 : F) * (a₂ ^ 2 - a₁ ^ 2) = 0 := by linear_combination ha₂ - ha₁
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h4)
  have hsb : b₂ ^ 2 = b₁ ^ 2 := by linear_combination hab₂ - hab₁ - hsa
  have hinv : (QuotientGroup.mk (B₁ * B₂) : PSL(2, F)) = 1 →
      (QuotientGroup.mk B₂ : PSL(2, F)) ∈ Subgroup.zpowers (QuotientGroup.mk B₁) := by
    intro hm
    have h' : (QuotientGroup.mk B₁ : PSL(2, F)) * QuotientGroup.mk B₂ = 1 := by
      rw [← QuotientGroup.mk_mul]
      exact hm
    rw [eq_inv_of_mul_eq_one_right h']
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsa with ha | ha <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsb with hb | hb
  ·
    have hE : B₂ = B₁ := Subtype.ext (by rw [h₂, h₁, ha, hb])
    rw [hE]
    exact Subgroup.mem_zpowers _
  ·
    apply hinv
    refine (p9_mk_eq_one_iff _).mpr ⟨1, by norm_num, ?_⟩
    rw [p9_scalar_one, Matrix.SpecialLinearGroup.coe_mul, h₁, h₂, ha, hb, p9Rot_mul]
    have e1 : a₁ * a₁ - b₁ * -b₁ = 1 := by linear_combination hab₁
    have e2 : a₁ * -b₁ + b₁ * a₁ = 0 := by ring
    rw [e1, e2, p9Rot_one]
  ·
    apply hinv
    refine (p9_mk_eq_one_iff _).mpr ⟨-1, by norm_num, ?_⟩
    rw [p9_scalar_neg_one, Matrix.SpecialLinearGroup.coe_mul, h₁, h₂, ha, hb, p9Rot_mul]
    have e1 : a₁ * -a₁ - b₁ * b₁ = -1 := by linear_combination -hab₁
    have e2 : a₁ * b₁ + b₁ * -a₁ = 0 := by ring
    rw [e1, e2, p9Rot_zero_eq_scalar, p9_scalar_neg_one]
  ·
    have hE : B₂ = B₁ * (-1) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one, mul_neg, mul_one, h₂, h₁, ha, hb, p9Rot_neg]
    rw [hE, QuotientGroup.mk_mul, p9_mk_neg_one, mul_one]
    exact Subgroup.mem_zpowers _

lemma p9_orderOf_nine {F : Type*} [Field F] (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (h9 : A ^ 9 = 1) (h3 : (QuotientGroup.mk (A ^ 3) : PSL(2, F)) ≠ 1) :
    orderOf (QuotientGroup.mk A : PSL(2, F)) = 9 := by
  have hA3 : ¬ (QuotientGroup.mk A : PSL(2, F)) ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← QuotientGroup.mk_pow]
    exact h3
  have hA9 : (QuotientGroup.mk A : PSL(2, F)) ^ 3 ^ (1 + 1) = 1 := by
    show (QuotientGroup.mk A : PSL(2, F)) ^ 9 = 1
    rw [← QuotientGroup.mk_pow, h9]
    simp
  have := orderOf_eq_prime_pow hA3 hA9
  norm_num at this
  exact this

lemma p9_exists_orderOf_nine {G : Type*} [Group G] [IsCyclic G] [Finite G]
    (h : 9 ∣ Nat.card G) : ∃ x : G, orderOf x = 9 := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h9le : 9 ≤ Nat.card G := Nat.le_of_dvd hpos h
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  refine ⟨g ^ (Nat.card G / 9), ?_⟩
  have hdvd : Nat.card G / 9 ∣ orderOf g := by
    rw [hg]
    exact Nat.div_dvd_of_dvd h
  have hne : Nat.card G / 9 ≠ 0 := (Nat.div_pos h9le (by norm_num)).ne'
  rw [orderOf_pow_of_dvd hne hdvd, hg]
  exact Nat.div_div_self h (by omega)

lemma p9_exists_t (q : ℕ) [Fact q.Prime] (h9 : 9 ∣ q - 1) :
    ∃ t : ZMod q, t ^ 9 = 1 ∧ t ^ 3 ≠ 1 := by
  have hcard : 9 ∣ Nat.card (ZMod q)ˣ := by
    rw [Nat.card_units, Nat.card_zmod]
    exact h9
  obtain ⟨u, hu⟩ := p9_exists_orderOf_nine hcard
  have hu9 : u ^ 9 = 1 := by
    rw [← hu]
    exact pow_orderOf_eq_one u
  refine ⟨(u : ZMod q), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, hu9, Units.val_one]
  · intro h
    have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have hdvd := orderOf_dvd_of_pow_eq_one hu3
    rw [hu] at hdvd
    norm_num at hdvd

lemma p9_split_exists {F : Type*} [Field F] (l t : F) (hl : l ^ 2 = -1) (h2 : (2 : F) ≠ 0)
    (ht9 : t ^ 9 = 1) (ht3 : t ^ 3 ≠ 1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F, orderOf (QuotientGroup.mk A : PSL(2, F)) = 9 ∧
      (A : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] =
        !![0, -1; 1, 0] * (A : Matrix (Fin 2) (Fin 2) F) := by
  have hl0 : l ≠ 0 := by
    rintro rfl
    norm_num at hl
  have ht0 : t ≠ 0 := by
    rintro rfl
    norm_num at ht9
  obtain ⟨s, hs⟩ : ∃ s : F, s = t⁻¹ := ⟨_, rfl⟩
  have hts : t * s = 1 := by
    rw [hs]
    exact mul_inv_cancel₀ ht0
  have hs9 : s ^ 9 = 1 := by
    rw [hs, inv_pow, ht9, inv_one]
  have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hinvl : (2 * l : F) * (2 * l)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero h2 hl0)
  obtain ⟨a, ha⟩ : ∃ a : F, a = (t + s) * 2⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : F, b = (t - s) * (2 * l)⁻¹ := ⟨_, rfl⟩
  have h2a : 2 * a = t + s := by
    rw [ha]
    linear_combination (t + s) * h22
  have h2b : 2 * (l * b) = t - s := by
    rw [hb]
    linear_combination (t - s) * hinvl
  have hat : a + l * b = t := mul_left_cancel₀ h2 (by linear_combination h2a + h2b)
  have hbt : a - l * b = s := mul_left_cancel₀ h2 (by linear_combination h2a - h2b)
  have hdet : a ^ 2 + b ^ 2 = 1 := by
    linear_combination (a - l * b) * hat + t * hbt + b ^ 2 * hl + hts
  have hdetA : (p9Rot a b).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet
  obtain ⟨A, hAval⟩ : ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      (A : Matrix (Fin 2) (Fin 2) F) = p9Rot a b := ⟨⟨p9Rot a b, hdetA⟩, rfl⟩
  have hcomm : (A : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] =
      !![0, -1; 1, 0] * (A : Matrix (Fin 2) (Fin 2) F) := by
    rw [hAval]
    exact psl2Conj_rot_comm_S a b
  have hpow : ∀ n : ℕ, ∃ p r : F, p9Rot a b ^ n = p9Rot p r ∧ p + l * r = t ^ n ∧
      p - l * r = s ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, 0, by rw [pow_zero, p9Rot_one], by simp, by simp⟩
    | succ n ih =>
      obtain ⟨p, r, hM, h1, h2'⟩ := ih
      refine ⟨p * a - r * b, p * b + r * a, ?_, ?_, ?_⟩
      · rw [pow_succ, hM, p9Rot_mul]
      · linear_combination (a + l * b) * h1 + t ^ n * hat - r * b * hl
      · linear_combination (a - l * b) * h2' + s ^ n * hbt - r * b * hl
  obtain ⟨p, r, hM9, h9a, h9b⟩ := hpow 9
  have hp : p = 1 := by
    have h : (2 : F) * (p - 1) = 0 := by linear_combination h9a + h9b + ht9 + hs9
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h2)
  have hr : r = 0 := by
    have h : (2 : F) * (l * r) = 0 := by linear_combination h9a - h9b + ht9 - hs9
    have h' : l * r = 0 := (mul_eq_zero.mp h).resolve_left h2
    exact (mul_eq_zero.mp h').resolve_left hl0
  have hA9 : A ^ 9 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hAval, hM9, hp, hr,
      p9Rot_one]
  have h3 : (QuotientGroup.mk (A ^ 3) : PSL(2, F)) ≠ 1 := by
    intro hm
    rw [p9_mk_eq_one_iff] at hm
    obtain ⟨x, hx, hxA⟩ := hm
    obtain ⟨p3, r3, hM3, h3a, h3b⟩ := hpow 3
    have hs1 : (Matrix.scalar (Fin 2) x) 1 0 = 0 := by
      simp [Matrix.scalar_apply, Matrix.diagonal_apply]
    have hs2 : (Matrix.scalar (Fin 2) x) 0 0 = x := by
      simp [Matrix.scalar_apply, Matrix.diagonal_apply]
    have e10 := congrFun (congrFun hxA 1) 0
    have e00 := congrFun (congrFun hxA 0) 0
    rw [Matrix.SpecialLinearGroup.coe_pow, hAval, hM3, hs1] at e10
    rw [Matrix.SpecialLinearGroup.coe_pow, hAval, hM3, hs2] at e00
    have hr3 : r3 = 0 := by
      simpa [p9Rot] using e10.symm
    have hp3 : p3 = x := by
      simpa [p9Rot] using e00.symm
    rw [hr3, mul_zero, add_zero, hp3] at h3a
    have h6 : t ^ 6 = 1 := by
      calc t ^ 6 = (t ^ 3) ^ 2 := by ring
        _ = x ^ 2 := by rw [← h3a]
        _ = 1 := hx
    apply ht3
    calc t ^ 3 = t ^ 6 * t ^ 3 := by rw [h6, one_mul]
      _ = t ^ 9 := by ring
      _ = 1 := ht9
  exact ⟨A, p9_orderOf_nine A hA9 h3, hcomm⟩

noncomputable abbrev p9Poly (F : Type*) [CommRing F] : Polynomial F := Polynomial.X ^ 2 + 1

lemma p9Poly_eq (F : Type*) [CommRing F] : p9Poly F = Polynomial.X ^ 2 + Polynomial.C 1 := by
  simp [p9Poly]

lemma p9Poly_natDegree (F : Type*) [CommRing F] [Nontrivial F] : (p9Poly F).natDegree = 2 := by
  rw [p9Poly_eq, Polynomial.natDegree_X_pow_add_C]

lemma p9Poly_monic (F : Type*) [CommRing F] [Nontrivial F] : (p9Poly F).Monic := by
  rw [p9Poly_eq]
  exact Polynomial.monic_X_pow_add_C _ two_ne_zero

lemma p9Poly_irreducible {F : Type*} [Field F] (hns : ¬ IsSquare (-1 : F)) :
    Irreducible (p9Poly F) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [p9Poly_natDegree, Finset.mem_Icc]
    norm_num
  · intro x hx
    apply hns
    refine ⟨x, ?_⟩
    have hx' : x ^ 2 + 1 = 0 := by
      simpa [p9Poly, Polynomial.IsRoot.def] using hx
    linear_combination -hx'

lemma p9_eq_one_of_pow_nine {F : Type*} [Field F] [Finite F] (q : ℕ) (hF : Nat.card F = q)
    (h9 : 9 ∣ q + 1) (hq3 : 3 ≤ q) (x : F) (hx : x ^ 9 = 1) : x = 1 := by
  haveI : Fintype F := Fintype.ofFinite F
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hx
    exact zero_ne_one hx
  have hferm : x ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx0
  have hcardF : Fintype.card F = q := by
    rw [← Nat.card_eq_fintype_card, hF]
  rw [hcardF] at hferm
  obtain ⟨k, hk⟩ := h9
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 4 * (q - 1) = 9 * m + 1 := ⟨4 * k - 1, by omega⟩
  have h4 : x ^ (4 * (q - 1)) = 1 := by
    rw [pow_mul', hferm, one_pow]
  rw [hm, pow_succ, pow_mul, hx, one_pow, one_mul] at h4
  exact h4

lemma p9_nonsplit_case {F : Type*} [Field F] [Finite F] (q : ℕ) (hF : Nat.card F = q)
    (hns : ¬ IsSquare (-1 : F)) (h9 : 9 ∣ q + 1) (hq3 : 3 ≤ q) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      orderOf (QuotientGroup.mk A : PSL(2, F)) = 9 ∧
      (A : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] =
        !![0, -1; 1, 0] * (A : Matrix (Fin 2) (Fin 2) F) := by
  haveI : Fact (Irreducible (p9Poly F)) := ⟨p9Poly_irreducible hns⟩
  haveI : Module.Finite F (AdjoinRoot (p9Poly F)) := (p9Poly_monic F).finite_adjoinRoot
  haveI : Finite (AdjoinRoot (p9Poly F)) := Module.finite_of_finite F
  have hfinrank : Module.finrank F (AdjoinRoot (p9Poly F)) = 2 := by
    rw [(AdjoinRoot.powerBasis' (p9Poly_monic F)).finrank]
    exact p9Poly_natDegree F
  have hcard : Nat.card (AdjoinRoot (p9Poly F)) = q ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), hfinrank, hF]
  have hunits : Nat.card (AdjoinRoot (p9Poly F))ˣ = q ^ 2 - 1 := by
    rw [Nat.card_units, hcard]
  have h9sq : 9 ∣ Nat.card (AdjoinRoot (p9Poly F))ˣ := by
    rw [hunits]
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    have e1 : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
    rw [e1, Nat.add_sub_cancel]
    exact Dvd.dvd.mul_left h9 m
  obtain ⟨ζ, hζ⟩ := p9_exists_orderOf_nine h9sq
  have hS2 : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) ^ 2 + 1 = 0 := by
    rw [sq, p9S_mul_self, neg_add_cancel]
  have hp0 : Polynomial.aeval (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) (p9Poly F) = 0 := by
    simp only [p9Poly, map_add, map_pow, Polynomial.aeval_X, map_one]
    exact hS2
  have hker : ∀ a ∈ Ideal.span ({p9Poly F} : Set (Polynomial F)),
      Polynomial.aeval (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) a = 0 := by
    intro a ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
    rw [hc, map_mul, hp0, zero_mul]
  let ev : AdjoinRoot (p9Poly F) →+* Matrix (Fin 2) (Fin 2) F :=
    Ideal.Quotient.lift (Ideal.span {p9Poly F})
      (Polynomial.aeval (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F)).toRingHom hker
  have hev_root : ev (AdjoinRoot.root (p9Poly F)) = !![0, -1; 1, 0] := by
    show Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ Polynomial.X) = _
    rw [Ideal.Quotient.lift_mk]
    simp
  have hev_of : ∀ x : F,
      ev (AdjoinRoot.of (p9Poly F) x) = algebraMap F (Matrix (Fin 2) (Fin 2) F) x := by
    intro x
    show Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ (Polynomial.C x)) = _
    rw [Ideal.Quotient.lift_mk]
    simp
  have hev_inj : Function.Injective ev := ev.injective
  have hscal : ∀ x : F, algebraMap F (Matrix (Fin 2) (Fin 2) F) x = Matrix.scalar (Fin 2) x := by
    intro x
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply, Matrix.diagonal_apply]
  have hζ9 : ζ ^ 9 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  have hζ3 : ζ ^ 3 ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at hdvd
    norm_num at hdvd
  obtain ⟨z, hz⟩ : ∃ z : AdjoinRoot (p9Poly F), z = (ζ : AdjoinRoot (p9Poly F)) := ⟨_, rfl⟩
  have hz9 : z ^ 9 = 1 := by
    rw [hz, ← Units.val_pow_eq_pow_val, hζ9, Units.val_one]
  have hz3 : z ^ 3 ≠ 1 := by
    intro h
    apply hζ3
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← hz]
    exact h
  have hA0_9 : (ev z) ^ 9 = 1 := by
    rw [← map_pow, hz9, map_one]
  have hdet : (ev z).det = 1 := by
    have hd9 : ((ev z).det) ^ 9 = 1 := by
      rw [← Matrix.det_pow, hA0_9, Matrix.det_one]
    exact p9_eq_one_of_pow_nine q hF h9 hq3 _ hd9
  have hcomm0 : ev z * !![0, -1; 1, 0] = !![0, -1; 1, 0] * ev z := by
    have h := congrArg ev (mul_comm z (AdjoinRoot.root (p9Poly F)))
    rw [map_mul, map_mul, hev_root] at h
    exact h
  obtain ⟨A, hA⟩ : ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      (A : Matrix (Fin 2) (Fin 2) F) = ev z := ⟨⟨ev z, hdet⟩, rfl⟩
  have hcomm : (A : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] =
      !![0, -1; 1, 0] * (A : Matrix (Fin 2) (Fin 2) F) := by
    rw [hA]
    exact hcomm0
  have hA9 : A ^ 9 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hA]
    exact hA0_9
  have h3 : (QuotientGroup.mk (A ^ 3) : PSL(2, F)) ≠ 1 := by
    intro hm
    rw [p9_mk_eq_one_iff] at hm
    obtain ⟨x, hx, hxA⟩ := hm
    have hcoe : ((A ^ 3 : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = ev (z ^ 3) := by
      rw [Matrix.SpecialLinearGroup.coe_pow, hA, map_pow]
    rw [hcoe, ← hscal, ← hev_of] at hxA
    have hinj := hev_inj hxA
    have h6 : z ^ 6 = 1 := by
      calc z ^ 6 = (z ^ 3) ^ 2 := by ring
        _ = (AdjoinRoot.of (p9Poly F) x) ^ 2 := by rw [hinj]
        _ = AdjoinRoot.of (p9Poly F) (x ^ 2) := (map_pow _ _ _).symm
        _ = 1 := by rw [hx, map_one]
    apply hz3
    calc z ^ 3 = z ^ 6 * z ^ 3 := by rw [h6, one_mul]
      _ = z ^ 9 := by ring
      _ = 1 := hz9
  exact ⟨A, p9_orderOf_nine A hA9 h3, hcomm⟩

lemma p9_four_ne_zero (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) : (4 : ZMod q) ≠ 0 := by
  have h4 : (4 : ZMod q) = 2 * 2 := by norm_num
  rw [h4]
  exact mul_ne_zero (psl2_two_ne_zero_zmod q hq) (psl2_two_ne_zero_zmod q hq)

lemma p9_split_case (q : ℕ) [Fact q.Prime] (hq4 : q % 4 = 1) (h9 : 9 ∣ q - 1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod q),
      orderOf (QuotientGroup.mk A : PSL(2, ZMod q)) = 9 ∧
      (A : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![0, -1; 1, 0] =
        !![0, -1; 1, 0] * (A : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  have hq2 : 2 ≤ q := (Fact.out : Nat.Prime q).two_le
  have hq3 : 3 ≤ q := by omega
  have hq4' : q % 4 ≠ 3 := by omega
  obtain ⟨l, hl⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := q)).mpr hq4'
  obtain ⟨t, ht9, ht3⟩ := p9_exists_t q h9
  have hl2 : l ^ 2 = -1 := by
    rw [sq]
    exact hl.symm
  exact p9_split_exists l t hl2 (psl2_two_ne_zero_zmod q hq3) ht9 ht3

lemma p9_nonsplit_case_zmod (q : ℕ) [Fact q.Prime] (hq4 : q % 4 = 3) (h9 : 9 ∣ q + 1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod q),
      orderOf (QuotientGroup.mk A : PSL(2, ZMod q)) = 9 ∧
      (A : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![0, -1; 1, 0] =
        !![0, -1; 1, 0] * (A : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  have hq3 : 3 ≤ q := by omega
  have hns : ¬ IsSquare (-1 : ZMod q) := by
    intro h
    have := ZMod.exists_sq_eq_neg_one_iff.mp h
    omega
  exact p9_nonsplit_case q (Nat.card_zmod q) hns h9 hq3

lemma p9_core (q : ℕ) [Fact q.Prime] (hq24 : q % 24 = 11 ∨ q % 24 = 13)
    (h9 : (9 : ℤ) ∣ (q : ℤ) - sgn4 q) :
    ∃ w : PSL(2, ZMod q), orderOf w = 9 ∧
      QuotientGroup.mk (p9S0 (ZMod q)) * w = w * QuotientGroup.mk (p9S0 (ZMod q)) ∧
      ∀ x : PSL(2, ZMod q), orderOf x = 3 →
        QuotientGroup.mk (p9S0 (ZMod q)) * x = x * QuotientGroup.mk (p9S0 (ZMod q)) →
          x ∈ Subgroup.zpowers (w ^ 3) := by
  have hq3 : 3 ≤ q := by omega
  obtain ⟨A, hA9, hAc⟩ : ∃ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod q),
      orderOf (QuotientGroup.mk A : PSL(2, ZMod q)) = 9 ∧
      (A : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![0, -1; 1, 0] =
        !![0, -1; 1, 0] * (A : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
    unfold sgn4 at h9
    split_ifs at h9 with hq4
    · exact p9_split_case q (by omega) (by omega)
    · exact p9_nonsplit_case_zmod q (by omega) (by omega)
  refine ⟨QuotientGroup.mk A, hA9, ?_, ?_⟩
  ·
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, p9_S0_coe]
    exact hAc.symm
  · intro x hx3 hxc
    obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective x
    rcases p9_comm_dichotomy B hxc.symm with hB | hB
    ·
      obtain ⟨hBform, hBab⟩ := p9_form_comm (B : Matrix (Fin 2) (Fin 2) (ZMod q)) B.2 hB
      have h4b := p9_order_three_of_rot B _ _ hBform hBab hx3
      have hAc' : Commute (A : Matrix (Fin 2) (Fin 2) (ZMod q)) !![0, -1; 1, 0] := hAc
      have hA3c : ((A ^ 3 : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :
          Matrix (Fin 2) (Fin 2) (ZMod q)) * !![0, -1; 1, 0] =
          !![0, -1; 1, 0] * ((A ^ 3 : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :
          Matrix (Fin 2) (Fin 2) (ZMod q)) := by
        rw [Matrix.SpecialLinearGroup.coe_pow]
        exact (hAc'.pow_left 3).eq
      obtain ⟨hA3form, hA3ab⟩ := p9_form_comm _ (A ^ 3).2 hA3c
      have h3ord : orderOf (QuotientGroup.mk (A ^ 3) : PSL(2, ZMod q)) = 3 := by
        have hdvd : 3 ∣ orderOf (QuotientGroup.mk A : PSL(2, ZMod q)) := by
          rw [hA9]
          norm_num
        rw [QuotientGroup.mk_pow, orderOf_pow_of_dvd (by norm_num) hdvd, hA9]
      have h4a := p9_order_three_of_rot (A ^ 3) _ _ hA3form hA3ab h3ord
      have hmem := p9_mk_mem_zpowers_of_rot (A ^ 3) B _ _ _ _ (p9_four_ne_zero q hq3)
        hA3form hBform hA3ab hBab h4a h4b
      rw [← QuotientGroup.mk_pow]
      exact hmem
    ·
      exfalso
      have h2 := p9_mk_sq_eq_one_of_anticomm B hB
      have hdvd := orderOf_dvd_of_pow_eq_one h2
      rw [hx3] at hdvd
      norm_num at hdvd

def p9Good {G : Type*} [Group G] (a : G) : Prop :=
  ∃ w : G, orderOf w = 9 ∧ a * w = w * a ∧
    ∀ x : G, orderOf x = 3 → a * x = x * a → x ∈ Subgroup.zpowers (w ^ 3)

lemma p9Good_of_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (a : G)
    (h : p9Good (φ a)) : p9Good a := by
  obtain ⟨w, hw9, hcomm, hsub⟩ := h
  refine ⟨φ.symm w, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hw9
  · apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hcomm
  · intro y hy3 hyc
    have hφy : orderOf (φ y) = 3 := by
      rw [MulEquiv.orderOf_eq]
      exact hy3
    have hcomm' : φ a * φ y = φ y * φ a := by
      rw [← map_mul, ← map_mul, hyc]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hsub (φ y) hφy hcomm')
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h' := congrArg φ.symm hk
    simp only [MulEquiv.symm_apply_apply, map_zpow, map_pow] at h'
    exact h'

theorem nfa2_P9L2 : Leaf_P9L2 := by
  intro q hq hq24 h9 Kb _ hKb a ha
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_psl_zmod hq hKb
  have hq3 : 3 ≤ q := by omega
  have hea : orderOf (e a) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ha
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (psl2_involutions_conj q hq3 (e a) (QuotientGroup.mk (p9S0 (ZMod q))) hea p9_orderOf_c0)
  let φ : Kb ≃* PSL(2, ZMod q) := e.trans (MulAut.conj g)
  have hφa : φ a = QuotientGroup.mk (p9S0 (ZMod q)) := by
    show MulAut.conj g (e a) = _
    rw [MulAut.conj_apply]
    exact hg
  refine p9Good_of_mulEquiv φ a ?_
  rw [hφa]
  exact p9_core q hq24 h9

end CFSG.Quasithin.H13.NFa2
