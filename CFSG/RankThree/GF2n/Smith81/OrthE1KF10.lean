module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

open scoped Matrix MatrixGroups
open CFSG.Open CFSG.Open.StatedAPI

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

section KF10

variable {K : Type} [Field K]

@[expose] def kf10Ad (g : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  (g : Matrix (Fin 2) (Fin 2) K) * X * ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)

@[expose] def kf10D (c : SL(2, K) → Matrix (Fin 2) (Fin 2) K) (g : SL(2, K)) :
    Matrix (Fin 2) (Fin 2) K :=
  c g * ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)

@[expose] def kf10Cyc (f : SL(2, K) → Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ g h : SL(2, K), f (g * h) = f g + kf10Ad g (f h)

lemma kf10_two_eq [CharP K 2] : (2 : K) = 0 := by
  exact_mod_cast CharP.cast_eq_zero K 2

lemma kf10_two [CharP K 2] (Y : Matrix (Fin 2) (Fin 2) K) : Y + Y = 0 :=
  Matrix.ext fun i j => CharTwo.add_self_eq_zero (Y i j)

lemma kf10_mul_inv_coe (g : SL(2, K)) :
    (g : Matrix (Fin 2) (Fin 2) K) * ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

lemma kf10_inv_mul_coe (g : SL(2, K)) :
    ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

lemma kf10Ad_mul (g h : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad (g * h) X = kf10Ad g (kf10Ad h X) := by
  simp only [kf10Ad, mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]

lemma kf10Ad_one (X : Matrix (Fin 2) (Fin 2) K) : kf10Ad 1 X = X := by
  simp [kf10Ad]

lemma kf10Ad_add (g : SL(2, K)) (X Y : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad g (X + Y) = kf10Ad g X + kf10Ad g Y := by
  simp only [kf10Ad, Matrix.mul_add, Matrix.add_mul]

lemma kf10Ad_zero (g : SL(2, K)) : kf10Ad g 0 = 0 := by
  simp [kf10Ad]

lemma kf10Ad_sum {ι : Type*} (s : Finset ι) (g : SL(2, K))
    (f : ι → Matrix (Fin 2) (Fin 2) K) :
    kf10Ad g (∑ i ∈ s, f i) = ∑ i ∈ s, kf10Ad g (f i) := by
  simp only [kf10Ad, Finset.mul_sum, Finset.sum_mul]

lemma kf10Ad_inv_ad (g : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad g⁻¹ (kf10Ad g X) = X := by
  rw [← kf10Ad_mul, inv_mul_cancel, kf10Ad_one]

lemma kf10_cyc_one {f : SL(2, K) → Matrix (Fin 2) (Fin 2) K} (hf : kf10Cyc f) : f 1 = 0 := by
  have h := hf 1 1
  rw [mul_one, kf10Ad_one] at h
  simpa using h

lemma kf10D_cyc (c : SL(2, K) → Matrix (Fin 2) (Fin 2) K)
    (hc : ∀ g h : SL(2, K), c (g * h) =
      (g : Matrix (Fin 2) (Fin 2) K) * c h + c g * (h : Matrix (Fin 2) (Fin 2) K)) :
    kf10Cyc (kf10D c) := by
  intro g h
  have hh' : (h : Matrix (Fin 2) (Fin 2) K) *
      (((h⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
        ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) =
      ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
    rw [← mul_assoc, kf10_mul_inv_coe h, one_mul]
  simp only [kf10D, kf10Ad, hc, mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.add_mul, Matrix.mul_add, mul_assoc, hh']
  exact add_comm _ _

lemma kf10_cyc_cob [CharP K 2] (X : Matrix (Fin 2) (Fin 2) K) :
    kf10Cyc (fun g => kf10Ad g X + X) := by
  intro g h
  simp only [kf10Ad_mul, kf10Ad_add]
  have hQ := kf10_two (kf10Ad g X)
  calc kf10Ad g (kf10Ad h X) + X
      = kf10Ad g (kf10Ad h X) + X + (kf10Ad g X + kf10Ad g X) := by rw [hQ, add_zero]
    _ = _ := by abel

lemma kf10_cyc_add {f f' : SL(2, K) → Matrix (Fin 2) (Fin 2) K} (hf : kf10Cyc f)
    (hf' : kf10Cyc f') : kf10Cyc (fun g => f g + f' g) := by
  intro g h
  simp only [hf g h, hf' g h, kf10Ad_add]
  abel

@[expose] def kf10Ker {f : SL(2, K) → Matrix (Fin 2) (Fin 2) K} (hf : kf10Cyc f) :
    Subgroup SL(2, K) where
  carrier := {g | f g = 0}
  one_mem' := kf10_cyc_one hf
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [hf a b, ha, hb, kf10Ad_zero, add_zero]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h := hf a a⁻¹
    rw [mul_inv_cancel, kf10_cyc_one hf, ha, zero_add] at h
    have h' := kf10Ad_inv_ad a (f a⁻¹)
    rw [← h, kf10Ad_zero] at h'
    exact h'.symm

@[expose] def kf10T (l : Kˣ) : SL(2, K) :=
  ⟨!![(l : K), 0; 0, (l : K)⁻¹], by simp [Matrix.det_fin_two_of]⟩

lemma kf10T_coe (l : Kˣ) :
    ((kf10T l : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![(l : K), 0; 0, (l : K)⁻¹] := rfl

lemma kf10T_inv_coe (l : Kˣ) :
    (((kf10T l)⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![(l : K)⁻¹, 0; 0, (l : K)] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, kf10T_coe]
  simp [Matrix.adjugate_fin_two]

lemma kf10T_mul (μ l : Kˣ) : kf10T μ * kf10T l = kf10T (μ * l) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, kf10T_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_inv] <;> ring

lemma kf10Ad_T (l : Kˣ) (Y : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad (kf10T l) Y =
      !![Y 0 0, (l : K) ^ 2 * Y 0 1; ((l : K)⁻¹) ^ 2 * Y 1 0, Y 1 1] := by
  have hl : (l : K) * (l : K)⁻¹ = 1 := mul_inv_cancel₀ l.ne_zero
  have hl' : (l : K)⁻¹ * (l : K) = 1 := inv_mul_cancel₀ l.ne_zero
  rw [kf10Ad, kf10T_inv_coe, kf10T_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    first
    | ring1
    | linear_combination (Y 0 0) * hl
    | linear_combination (Y 1 1) * hl'

lemma kf10Ad_T_00 (l : Kˣ) (Y : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad (kf10T l) Y 0 0 = Y 0 0 := by
  rw [kf10Ad_T]; simp

lemma kf10Ad_T_11 (l : Kˣ) (Y : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad (kf10T l) Y 1 1 = Y 1 1 := by
  rw [kf10Ad_T]; simp

lemma kf10Ad_T_01 (l : Kˣ) (Y : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad (kf10T l) Y 0 1 = (l : K) ^ 2 * Y 0 1 := by
  rw [kf10Ad_T]; simp

lemma kf10Ad_T_10 (l : Kˣ) (Y : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad (kf10T l) Y 1 0 = ((l : K)⁻¹) ^ 2 * Y 1 0 := by
  rw [kf10Ad_T]; simp

@[expose] def kf10U (a : K) : SL(2, K) := ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def kf10V (a : K) : SL(2, K) := ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def kf10W [CharP K 2] : SL(2, K) :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two_of, CharTwo.neg_eq]⟩

lemma kf10U_coe (a : K) :
    ((kf10U a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, a; 0, 1] := rfl

lemma kf10V_coe (a : K) :
    ((kf10V a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; a, 1] := rfl

lemma kf10W_coe [CharP K 2] :
    ((kf10W : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

lemma kf10U_inv_coe (a : K) :
    (((kf10U a)⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, -a; 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, kf10U_coe]
  simp [Matrix.adjugate_fin_two]

lemma kf10Ad_U (a : K) (Y : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad (kf10U a) Y = !![Y 0 0 + a * Y 1 0, Y 0 1 - a * Y 0 0 - a * a * Y 1 0 + a * Y 1 1;
      Y 1 0, Y 1 1 - a * Y 1 0] := by
  rw [kf10Ad, kf10U_inv_coe, kf10U_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

lemma kf10Ad_U_00 (a : K) (Y : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad (kf10U a) Y 0 0 = Y 0 0 + a * Y 1 0 := by
  rw [kf10Ad_U]; simp

lemma kf10Ad_U_01 (a : K) (Y : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad (kf10U a) Y 0 1 = Y 0 1 - a * Y 0 0 - a * a * Y 1 0 + a * Y 1 1 := by
  rw [kf10Ad_U]; simp

lemma kf10Ad_U_10 (a : K) (Y : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad (kf10U a) Y 1 0 = Y 1 0 := by
  rw [kf10Ad_U]; simp

lemma kf10Ad_U_11 (a : K) (Y : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad (kf10U a) Y 1 1 = Y 1 1 - a * Y 1 0 := by
  rw [kf10Ad_U]; simp

lemma kf10U_mul (a b : K) : kf10U a * kf10U b = kf10U (a + b) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, kf10U_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

lemma kf10U_zero : kf10U (0 : K) = 1 := by
  apply Subtype.ext
  rw [kf10U_coe, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma kf10T_mul_U (l : Kˣ) (a : K) :
    kf10T l * kf10U a = kf10U ((l : K) ^ 2 * a) * kf10T l := by
  have hl : (l : K) * (l : K)⁻¹ = 1 := mul_inv_cancel₀ l.ne_zero
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, kf10T_coe, kf10U_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    first
    | ring1
    | linear_combination (-((l : K) * a)) * hl

lemma kf10W_mul_self [CharP K 2] : (kf10W : SL(2, K)) * kf10W = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, kf10W_coe, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

lemma kf10Ad_W [CharP K 2] (Y : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad kf10W Y = !![Y 1 1, Y 1 0; Y 0 1, Y 0 0] := by
  have hinv : (((kf10W : SL(2, K))⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![0, 1; 1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, kf10W_coe]
    simp [Matrix.adjugate_fin_two, CharTwo.neg_eq]
  rw [kf10Ad, hinv, kf10W_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

lemma kf10Ad_W_00 [CharP K 2] (Y : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad kf10W Y 0 0 = Y 1 1 := by
  rw [kf10Ad_W]; simp

lemma kf10Ad_W_W [CharP K 2] (X : Matrix (Fin 2) (Fin 2) K) :
    kf10Ad kf10W (kf10Ad kf10W X) = X := by
  rw [← kf10Ad_mul, kf10W_mul_self, kf10Ad_one]

lemma kf10W_mul_T_mul_W [CharP K 2] (l : Kˣ) : kf10W * kf10T l * kf10W = kf10T l⁻¹ := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, kf10W_coe, kf10T_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

lemma kf10W_mul_U_mul_W [CharP K 2] (a : K) : kf10W * kf10U a * kf10W = kf10V a := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, kf10W_coe, kf10U_coe, kf10V_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

lemma kf10_transvection_U (a : K) (h : (0 : Fin 2) ≠ 1) :
    Matrix.TransvectionStruct.toSpecialLinearGroup
      (⟨0, 1, h, a⟩ : Matrix.TransvectionStruct (Fin 2) K) = kf10U a := by
  apply Subtype.ext
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_coe, kf10U_coe,
    Matrix.TransvectionStruct.toMatrix_mk, Matrix.transvection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

lemma kf10_transvection_V (a : K) (h : (1 : Fin 2) ≠ 0) :
    Matrix.TransvectionStruct.toSpecialLinearGroup
      (⟨1, 0, h, a⟩ : Matrix.TransvectionStruct (Fin 2) K) = kf10V a := by
  apply Subtype.ext
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_coe, kf10V_coe,
    Matrix.TransvectionStruct.toMatrix_mk, Matrix.transvection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

lemma kf10_gen {f : SL(2, K) → Matrix (Fin 2) (Fin 2) K} (hf : kf10Cyc f)
    (hU : ∀ a : K, f (kf10U a) = 0) (hV : ∀ a : K, f (kf10V a) = 0) (g : SL(2, K)) :
    f g = 0 := by
  have hle : Subgroup.closure (Set.range
      (Matrix.TransvectionStruct.toSpecialLinearGroup :
        Matrix.TransvectionStruct (Fin 2) K → SL(2, K))) ≤ kf10Ker hf := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨i, j, hij, a⟩, rfl⟩
    rcases (show (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) by
      revert hij; revert i j; decide) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show f _ = 0
      rw [kf10_transvection_U a hij]
      exact hU a
    · show f _ = 0
      rw [kf10_transvection_V a hij]
      exact hV a
  have htop := Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 2) (K := K)
  have hmem : g ∈ Subgroup.closure (Set.range
      (Matrix.TransvectionStruct.toSpecialLinearGroup :
        Matrix.TransvectionStruct (Fin 2) K → SL(2, K))) := by
    rw [htop]
    exact Subgroup.mem_top g
  exact hle hmem

lemma kf10_exists_ne [Finite K] (hq : 4 ≤ Nat.card K) : ∃ c0 : K, c0 ≠ 0 ∧ c0 ≠ 1 := by
  by_contra h
  have h' : ∀ c0 : K, c0 ≠ 0 → c0 = 1 := fun c0 h0 => by
    by_contra h1
    exact h ⟨c0, h0, h1⟩
  letI : Fintype K := Fintype.ofFinite K
  have hsurj : Function.Surjective (fun i : Fin 2 => if i = 0 then (0 : K) else 1) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [h' x hx]⟩
  have hle := Fintype.card_le_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card] at hq
  simp only [Fintype.card_fin] at hle
  omega

lemma kf10_sqrt [Finite K] [CharP K 2] (μ : K) (hμ : μ ≠ 0) :
    ∃ l : Kˣ, (l : K) ^ 2 = μ := by
  have hinj : Function.Injective (fun x : K => x ^ 2) := by
    intro x y hxy
    have hxy' : x ^ 2 = y ^ 2 := hxy
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hxy' with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hinj μ
  have hx' : x ^ 2 = μ := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hμ (by rw [← hx']; simp)
  exact ⟨Units.mk0 x hx0, by simpa using hx'⟩

lemma kf10_card [Fintype K] [DecidableEq K] [CharP K 2] (hq : 4 ≤ Fintype.card K) :
    ((Fintype.card Kˣ : ℕ) : K) = 1 := by
  have hev : Fintype.card K % 2 = 0 := FiniteField.even_card_iff_char_two.1 (ringChar.eq K 2)
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card K = 2 * m := ⟨Fintype.card K / 2, by omega⟩
  rw [Fintype.card_units, show Fintype.card K - 1 = 2 * (m - 1) + 1 by omega]
  push_cast
  rw [kf10_two_eq]
  ring

lemma kf10_torus [Fintype K] [DecidableEq K] [CharP K 2] (hq : 4 ≤ Fintype.card K)
    {c : SL(2, K) → Matrix (Fin 2) (Fin 2) K} (hc : kf10Cyc (kf10D c)) (μ : Kˣ) :
    kf10D c (kf10T μ) = (∑ l : Kˣ, kf10D c (kf10T l)) +
      kf10Ad (kf10T μ) (∑ l : Kˣ, kf10D c (kf10T l)) := by
  have hcard := kf10_card hq
  have h1 : ∑ l : Kˣ, kf10D c (kf10T (μ * l)) = ∑ l : Kˣ, kf10D c (kf10T l) :=
    Equiv.sum_comp (Equiv.mulLeft μ) (fun l => kf10D c (kf10T l))
  have h2 : ∑ l : Kˣ, kf10D c (kf10T μ * kf10T l) =
      ∑ l : Kˣ, (kf10D c (kf10T μ) + kf10Ad (kf10T μ) (kf10D c (kf10T l))) :=
    Finset.sum_congr rfl (fun l _ => hc _ _)
  have h3 : ∑ l : Kˣ, kf10Ad (kf10T μ) (kf10D c (kf10T l)) =
      kf10Ad (kf10T μ) (∑ l : Kˣ, kf10D c (kf10T l)) :=
    (kf10Ad_sum Finset.univ _ _).symm
  simp only [kf10T_mul] at h2
  rw [h1, Finset.sum_add_distrib, h3, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul K, hcard, one_smul] at h2
  have hA := kf10_two (kf10Ad (kf10T μ) (∑ l : Kˣ, kf10D c (kf10T l)))
  calc kf10D c (kf10T μ)
      = (kf10D c (kf10T μ) + kf10Ad (kf10T μ) (∑ l : Kˣ, kf10D c (kf10T l))) +
          kf10Ad (kf10T μ) (∑ l : Kˣ, kf10D c (kf10T l)) := by
        rw [add_assoc, hA, add_zero]
    _ = _ := by rw [← h2]

lemma kf10_alg [CharP K 2] {c x s z w : K} (hc1 : c ≠ 1)
    (E1 : x = x + (x + s)) (E2 : w = w + (w - s)) (E3 : x = x + (x + c * z))
    (E5 : s * c = z) : x = 0 ∧ z = 0 ∧ w = 0 := by
  have h2 := kf10_two_eq (K := K)
  have hne1 : (1 : K) + c ≠ 0 := by
    intro h
    apply hc1
    linear_combination h - h2
  have hne2 : 1 + c ^ 2 ≠ 0 := by
    intro h
    have h' : (1 + c) ^ 2 = 0 := by linear_combination h + c * h2
    exact hne1 ((pow_eq_zero_iff two_ne_zero).1 h')
  have hG : (1 + c ^ 2) * x = 0 := by
    linear_combination (-1 : K) * E3 + c ^ 2 * E1 + c * E5 + (c ^ 2 * x) * h2
  have hx : x = 0 := (mul_eq_zero.1 hG).resolve_left hne2
  have hs : s = 0 := by linear_combination (-1 : K) * E1 - hx
  have hz : z = 0 := by rw [← E5, hs, zero_mul]
  have hw : w = 0 := by linear_combination (-1 : K) * E2 + hs
  exact ⟨hx, hz, hw⟩

lemma kf10_unip [Finite K] [CharP K 2] (hc0 : ∃ c0 : K, c0 ≠ 0 ∧ c0 ≠ 1)
    {D₁ : SL(2, K) → Matrix (Fin 2) (Fin 2) K} (hD₁ : kf10Cyc D₁)
    (hT : ∀ l : Kˣ, D₁ (kf10T l) = 0) :
    ∃ y : K, ∀ a : K, D₁ (kf10U a) = !![0, a * y; 0, 0] := by
  obtain ⟨c0, hc00, hc01⟩ := hc0
  have hC1 : ∀ a b : K, D₁ (kf10U (a + b)) =
      D₁ (kf10U a) + kf10Ad (kf10U a) (D₁ (kf10U b)) := by
    intro a b
    rw [← kf10U_mul, hD₁ (kf10U a) (kf10U b)]
  have hC2 : ∀ (l : Kˣ) (a : K),
      D₁ (kf10U ((l : K) ^ 2 * a)) = kf10Ad (kf10T l) (D₁ (kf10U a)) := by
    intro l a
    have h := hD₁ (kf10T l) (kf10U a)
    rw [kf10T_mul_U, hD₁ (kf10U ((l : K) ^ 2 * a)) (kf10T l), hT l, kf10Ad_zero, add_zero,
      zero_add] at h
    exact h
  have hμ : ∀ μ : K, μ ≠ 0 →
      D₁ (kf10U μ) 0 0 = D₁ (kf10U 1) 0 0 ∧ D₁ (kf10U μ) 1 1 = D₁ (kf10U 1) 1 1 ∧
      D₁ (kf10U μ) 0 1 = μ * D₁ (kf10U 1) 0 1 ∧
      D₁ (kf10U μ) 1 0 * μ = D₁ (kf10U 1) 1 0 := by
    intro μ hμ0
    obtain ⟨l, hl⟩ := kf10_sqrt μ hμ0
    have h := hC2 l 1
    rw [mul_one, hl] at h
    have hl' : (l : K)⁻¹ * (l : K) = 1 := inv_mul_cancel₀ l.ne_zero
    rw [h]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [kf10Ad_T_00]
    · rw [kf10Ad_T_11]
    · rw [kf10Ad_T_01, ← hl]
    · rw [kf10Ad_T_10, ← hl]
      linear_combination (D₁ (kf10U 1) 1 0 * ((l : K)⁻¹ * (l : K) + 1)) * hl'
  have hne1 : (1 : K) + c0 ≠ 0 := by
    intro h
    apply hc01
    linear_combination h - kf10_two_eq (K := K)
  have E1 : D₁ (kf10U 1) 0 0 = D₁ (kf10U 1) 0 0 + (D₁ (kf10U 1) 0 0 + D₁ (kf10U c0) 1 0) := by
    have e := congrFun (congrFun (hC1 1 c0) 0) 0
    rw [Matrix.add_apply, kf10Ad_U_00, (hμ (1 + c0) hne1).1, (hμ c0 hc00).1, one_mul] at e
    exact e
  have E2 : D₁ (kf10U 1) 1 1 = D₁ (kf10U 1) 1 1 + (D₁ (kf10U 1) 1 1 - D₁ (kf10U c0) 1 0) := by
    have e := congrFun (congrFun (hC1 1 c0) 1) 1
    rw [Matrix.add_apply, kf10Ad_U_11, (hμ (1 + c0) hne1).2.1, (hμ c0 hc00).2.1, one_mul] at e
    exact e
  have E3 : D₁ (kf10U 1) 0 0 =
      D₁ (kf10U 1) 0 0 + (D₁ (kf10U 1) 0 0 + c0 * D₁ (kf10U 1) 1 0) := by
    have e := congrFun (congrFun (hC1 c0 1) 0) 0
    rw [add_comm c0 1, Matrix.add_apply, kf10Ad_U_00, (hμ (1 + c0) hne1).1,
      (hμ c0 hc00).1] at e
    exact e
  have E5 : D₁ (kf10U c0) 1 0 * c0 = D₁ (kf10U 1) 1 0 := (hμ c0 hc00).2.2.2
  obtain ⟨hx, hz, hw⟩ := kf10_alg hc01 E1 E2 E3 E5
  refine ⟨D₁ (kf10U 1) 0 1, fun a => ?_⟩
  by_cases ha : a = 0
  · subst ha
    rw [kf10U_zero, kf10_cyc_one hD₁]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · obtain ⟨h1, h2, h3, h4⟩ := hμ a ha
    have h4' : D₁ (kf10U a) 1 0 = 0 := (mul_eq_zero.1 (h4.trans hz)).resolve_right ha
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4', hx, hw]

lemma kf10_weyl [CharP K 2] {D₂ : SL(2, K) → Matrix (Fin 2) (Fin 2) K} (hD₂ : kf10Cyc D₂)
    (hc0 : ∃ c0 : K, c0 ≠ 0 ∧ c0 ≠ 1) (hT : ∀ l : Kˣ, D₂ (kf10T l) = 0)
    (hU : ∀ a : K, D₂ (kf10U a) = 0) : ∀ g : SL(2, K), D₂ g = 0 := by
  obtain ⟨c0, hc00, hc01⟩ := hc0
  have h2 := kf10_two_eq (K := K)
  obtain ⟨N, hN⟩ : ∃ N, D₂ kf10W = N := ⟨_, rfl⟩
  have hWN : kf10Ad kf10W N = N := by
    have h := hD₂ kf10W kf10W
    rw [kf10W_mul_self, kf10_cyc_one hD₂, hN] at h
    have hA := kf10_two (kf10Ad kf10W N)
    calc kf10Ad kf10W N = 0 + kf10Ad kf10W N := (zero_add _).symm
      _ = (N + kf10Ad kf10W N) + kf10Ad kf10W N := by rw [← h]
      _ = N + (kf10Ad kf10W N + kf10Ad kf10W N) := by abel
      _ = N := by rw [hA, add_zero]
  have hTW : ∀ l : Kˣ, kf10Ad (kf10T l) N = N := by
    intro l
    have h1 : D₂ (kf10W * kf10T l) = N := by
      rw [hD₂ kf10W (kf10T l), hT l, kf10Ad_zero, add_zero, hN]
    have h2' := hD₂ (kf10W * kf10T l) kf10W
    rw [kf10W_mul_T_mul_W, hT (l⁻¹), h1, hN] at h2'
    have hA : kf10Ad (kf10W * kf10T l) N = N := by
      have hA2 := kf10_two (kf10Ad (kf10W * kf10T l) N)
      calc kf10Ad (kf10W * kf10T l) N = 0 + kf10Ad (kf10W * kf10T l) N := (zero_add _).symm
        _ = (N + kf10Ad (kf10W * kf10T l) N) + kf10Ad (kf10W * kf10T l) N := by rw [← h2']
        _ = N + (kf10Ad (kf10W * kf10T l) N + kf10Ad (kf10W * kf10T l) N) := by abel
        _ = N := by rw [hA2, add_zero]
    calc kf10Ad (kf10T l) N = kf10Ad kf10W (kf10Ad kf10W (kf10Ad (kf10T l) N)) :=
          (kf10Ad_W_W _).symm
      _ = kf10Ad kf10W N := by rw [← kf10Ad_mul kf10W (kf10T l) N, hA]
      _ = N := hWN
  have hu : ((Units.mk0 c0 hc00 : Kˣ) : K) = c0 := Units.val_mk0 hc00
  have e01 : c0 ^ 2 * N 0 1 = N 0 1 := by
    have h := congrFun (congrFun (hTW (Units.mk0 c0 hc00)) 0) 1
    rw [kf10Ad_T_01, hu] at h
    exact h
  have e10 : c0⁻¹ ^ 2 * N 1 0 = N 1 0 := by
    have h := congrFun (congrFun (hTW (Units.mk0 c0 hc00)) 1) 0
    rw [kf10Ad_T_10, hu] at h
    exact h
  have hinv : c0 * c0⁻¹ = 1 := mul_inv_cancel₀ hc00
  have e10' : c0 ^ 2 * N 1 0 = N 1 0 := by
    linear_combination (-c0 ^ 2) * e10 + N 1 0 * (c0 * c0⁻¹ + 1) * hinv
  have hne : c0 ^ 2 + 1 ≠ 0 := by
    intro h
    have h' : (c0 + 1) ^ 2 = 0 := by linear_combination h + c0 * h2
    apply hc01
    have h'' : c0 + 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 h'
    linear_combination h'' - h2
  have hN01 : N 0 1 = 0 := by
    have h : (c0 ^ 2 + 1) * N 0 1 = 0 := by linear_combination e01 + N 0 1 * h2
    exact (mul_eq_zero.1 h).resolve_left hne
  have hN10 : N 1 0 = 0 := by
    have h : (c0 ^ 2 + 1) * N 1 0 = 0 := by linear_combination e10' + N 1 0 * h2
    exact (mul_eq_zero.1 h).resolve_left hne
  have hdiag : N 0 0 = N 1 1 := by
    have h := congrFun (congrFun hWN 0) 0
    rw [kf10Ad_W_00] at h
    exact h.symm
  have hVN : ∀ a : K, kf10Ad (kf10U a) N = N := by
    intro a
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kf10Ad_U_00, kf10Ad_U_01, kf10Ad_U_10, kf10Ad_U_11, hN01, hN10, hdiag] <;> ring
  have hV : ∀ a : K, D₂ (kf10V a) = 0 := by
    intro a
    rw [← kf10W_mul_U_mul_W a, hD₂ (kf10W * kf10U a) kf10W, hD₂ kf10W (kf10U a), hU a,
      kf10Ad_zero, add_zero, hN, kf10Ad_mul, hVN a, hWN, kf10_two]
  exact fun g => kf10_gen hD₂ hU hV g

theorem kf10_sl2 [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (c : SL(2, K) → Matrix (Fin 2) (Fin 2) K)
    (hc : ∀ g h : SL(2, K), c (g * h) =
      (g : Matrix (Fin 2) (Fin 2) K) * c h + c g * (h : Matrix (Fin 2) (Fin 2) K)) :
    ∃ m : Matrix (Fin 2) (Fin 2) K, ∀ g : SL(2, K),
      c g = (g : Matrix (Fin 2) (Fin 2) K) * m - m * (g : Matrix (Fin 2) (Fin 2) K) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hq' : 4 ≤ Fintype.card K := by rw [← Nat.card_eq_fintype_card]; exact hq
  have hc0 := kf10_exists_ne hq
  have h2 := kf10_two_eq (K := K)
  have hD : kf10Cyc (kf10D c) := kf10D_cyc c hc
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 2) (Fin 2) K, S = ∑ l : Kˣ, kf10D c (kf10T l) :=
    ⟨_, rfl⟩
  have htor : ∀ l : Kˣ, kf10D c (kf10T l) = S + kf10Ad (kf10T l) S := by
    intro l
    rw [hS]
    exact kf10_torus hq' hD l
  have hD₁ : kf10Cyc (fun g => kf10D c g + (kf10Ad g S + S)) :=
    kf10_cyc_add hD (kf10_cyc_cob S)
  have hT₁ : ∀ l : Kˣ, kf10D c (kf10T l) + (kf10Ad (kf10T l) S + S) = 0 := by
    intro l
    rw [htor l]
    have hA := kf10_two (kf10Ad (kf10T l) S)
    have hB := kf10_two S
    calc S + kf10Ad (kf10T l) S + (kf10Ad (kf10T l) S + S)
        = (S + S) + (kf10Ad (kf10T l) S + kf10Ad (kf10T l) S) := by abel
      _ = 0 := by rw [hB, hA, add_zero]
  obtain ⟨y, hy⟩ := kf10_unip hc0 hD₁ hT₁
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : Matrix (Fin 2) (Fin 2) K, m₁ = !![y, 0; 0, 0] := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : Matrix (Fin 2) (Fin 2) K, m = S + m₁ := ⟨_, rfl⟩
  have hE : kf10Cyc (fun g => kf10D c g + (kf10Ad g m + m)) :=
    kf10_cyc_add hD (kf10_cyc_cob m)
  have hid : ∀ g : SL(2, K), kf10D c g + (kf10Ad g m + m) =
      (kf10D c g + (kf10Ad g S + S)) + (kf10Ad g m₁ + m₁) := by
    intro g
    rw [hm, kf10Ad_add]
    abel
  have hm1T : ∀ l : Kˣ, kf10Ad (kf10T l) m₁ = m₁ := by
    intro l
    rw [hm₁, kf10Ad_T]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hTE : ∀ l : Kˣ, kf10D c (kf10T l) + (kf10Ad (kf10T l) m + m) = 0 := by
    intro l
    rw [htor l, hm, kf10Ad_add, hm1T l]
    have hA := kf10_two (kf10Ad (kf10T l) S)
    have hB := kf10_two S
    have hC := kf10_two m₁
    calc S + kf10Ad (kf10T l) S + (kf10Ad (kf10T l) S + m₁ + (S + m₁))
        = (S + S) + (kf10Ad (kf10T l) S + kf10Ad (kf10T l) S) + (m₁ + m₁) := by abel
      _ = 0 := by rw [hB, hA, hC, add_zero, add_zero]
  have hUE : ∀ a : K, kf10D c (kf10U a) + (kf10Ad (kf10U a) m + m) = 0 := by
    intro a
    rw [hid]
    have hy' : kf10D c (kf10U a) + (kf10Ad (kf10U a) S + S) = !![0, a * y; 0, 0] := hy a
    rw [hy', hm₁]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kf10Ad_U_00, kf10Ad_U_01, kf10Ad_U_10, kf10Ad_U_11, CharTwo.add_self_eq_zero]
  refine ⟨m, fun g => ?_⟩
  have hg : kf10D c g + (kf10Ad g m + m) = 0 := kf10_weyl hE hc0 hTE hUE g
  have hDg : kf10D c g = kf10Ad g m + m := by
    have hA := kf10_two (kf10Ad g m + m)
    calc kf10D c g = (kf10D c g + (kf10Ad g m + m)) + (kf10Ad g m + m) := by
          rw [add_assoc, hA, add_zero]
      _ = kf10Ad g m + m := by rw [hg, zero_add]
  have hcg : c g = kf10D c g * (g : Matrix (Fin 2) (Fin 2) K) := by
    rw [kf10D, mul_assoc, kf10_inv_mul_coe, mul_one]
  have hcalc : (kf10Ad g m + m) * (g : Matrix (Fin 2) (Fin 2) K) =
      (g : Matrix (Fin 2) (Fin 2) K) * m + m * (g : Matrix (Fin 2) (Fin 2) K) := by
    simp only [kf10Ad, Matrix.add_mul, Matrix.mul_assoc, kf10_inv_mul_coe, mul_one]
  rw [hcg, hDg, hcalc, sub_eq_add_neg, CharTwo.neg_eq]

end KF10

theorem h1Tensor_holds : H1TensorStatement := by
  intro K _ _ _ hq c hc
  let ι : SL(2, K) → ↥(StatedSL 2 K) := fun g =>
    ⟨Matrix.SpecialLinearGroup.toGL g, mem_statedSL_of_det g.2⟩
  have hι : ∀ g h : SL(2, K), ι (g * h) = ι g * ι h := fun g h =>
    Subtype.ext (map_mul _ g h)
  have hc' : ∀ g h : SL(2, K), c (ι (g * h)) =
      (g : Matrix (Fin 2) (Fin 2) K) * c (ι h) + c (ι g) * (h : Matrix (Fin 2) (Fin 2) K) := by
    intro g h
    rw [hι]
    exact hc (ι g) (ι h)
  obtain ⟨m, hm⟩ := kf10_sl2 hq (fun g => c (ι g)) hc'
  refine ⟨m, fun g => ?_⟩
  obtain ⟨g', rfl⟩ : ∃ g' : SL(2, K), ι g' = g :=
    ⟨⟨(g : GL (Fin 2) K).val, mem_statedSL_iff.1 g.2⟩, Subtype.ext (Units.ext rfl)⟩
  exact hm g'

end CFSG.RankThree.GF2n.Smith81.Smith23E1
