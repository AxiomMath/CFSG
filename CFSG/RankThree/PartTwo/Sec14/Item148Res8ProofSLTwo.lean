module

import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix

variable {K : Type} [Field K]

abbrev uSL (x : K) : SpecialLinearGroup (Fin 2) K :=
  SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) x

abbrev lSL (y : K) : SpecialLinearGroup (Fin 2) K :=
  SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) y

theorem uSL_coe (x : K) : ((uSL x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, x; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe]

theorem lSL_coe (y : K) : ((lSL y : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, 0; y, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe]

theorem uSL_injective : Function.Injective (uSL : K → SpecialLinearGroup (Fin 2) K) := by
  intro x y h
  have h1 := congrFun (congrFun (congrArg Subtype.val h) 0) 1
  rw [uSL_coe, uSL_coe] at h1
  simpa using h1

theorem uSL_mul (x y : K) : uSL x * uSL y = uSL (x + y) :=
  (SpecialLinearGroup.transvection_add _ x y).symm

theorem exists_eq_uSL_of_commute [CharP K 2] {A : SpecialLinearGroup (Fin 2) K} {c : K}
    (hc : c ≠ 0) (h : A * uSL c = uSL c * A) : ∃ b : K, A = uSL b := by
  have hM : (A : Matrix (Fin 2) (Fin 2) K) * !![1, c; 0, 1] =
      !![1, c; 0, 1] * (A : Matrix (Fin 2) (Fin 2) K) := by
    rw [← uSL_coe]
    exact congrArg (fun X : SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) h
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have h10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := e00.resolve_left hc
  have hd : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = (A : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have : c * ((A : Matrix (Fin 2) (Fin 2) K) 1 1 - (A : Matrix (Fin 2) (Fin 2) K) 0 0) = 0 := by
      linear_combination -e01
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc)
  have hdet := A.2
  rw [Matrix.det_fin_two, h10, hd, mul_zero, sub_zero] at hdet
  have ha : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have h2 : ((A : Matrix (Fin 2) (Fin 2) K) 0 0 + 1) ^ 2 = 0 := by
      have h2' : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination hdet + ((A : Matrix (Fin 2) (Fin 2) K) 0 0 + 1) * h2'
    have h3 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    have h2' : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination h3 - h2'
  refine ⟨(A : Matrix (Fin 2) (Fin 2) K) 0 1, Subtype.ext ?_⟩
  rw [uSL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, h10, hd]

theorem trace_eq_zero_of_commute_involution [CharP K 2] {A T : SpecialLinearGroup (Fin 2) K}
    (hT2 : T * T = 1) (hT1 : T ≠ 1) (h : A * T = T * A) :
    (A : Matrix (Fin 2) (Fin 2) K) 0 0 + (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set a := (A : Matrix (Fin 2) (Fin 2) K) with ha
  set t := (T : Matrix (Fin 2) (Fin 2) K) with ht
  have hTT : t * t = 1 :=
    congrArg (fun X : SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) hT2
  have hAT : a * t = t * a :=
    congrArg (fun X : SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) h
  have t00 := congrFun (congrFun hTT 0) 0
  have t01 := congrFun (congrFun hTT 0) 1
  have t10 := congrFun (congrFun hTT 1) 0
  have t11 := congrFun (congrFun hTT 1) 1
  have a00 := congrFun (congrFun hAT 0) 0
  have a01 := congrFun (congrFun hAT 0) 1
  have a10 := congrFun (congrFun hAT 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at t00 t01 t10 t11 a00 a01 a10
  have htr : t 0 0 + t 1 1 = 0 := by
    have : (t 0 0 + t 1 1) ^ 2 = 0 := by
      linear_combination t00 + t11 + (t 0 0 * t 1 1 - t 0 1 * t 1 0 + 1) * h2
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  by_contra hne
  have hdiff : a 0 0 - a 1 1 ≠ 0 := by
    intro h0
    apply hne
    linear_combination h0 + a 1 1 * h2
  have h01 : t 0 1 = 0 := by
    have : (a 0 0 - a 1 1) * t 0 1 = 0 := by
      linear_combination a01 + a 0 1 * htr - a 0 1 * t 1 1 * h2
    exact (mul_eq_zero.mp this).resolve_left hdiff
  have h10 : t 1 0 = 0 := by
    have : (a 0 0 - a 1 1) * t 1 0 = 0 := by
      linear_combination -a10 + a 1 0 * htr - a 1 0 * t 1 1 * h2
    exact (mul_eq_zero.mp this).resolve_left hdiff
  have h00 : t 0 0 = 1 := by
    have : (t 0 0 + 1) ^ 2 = 0 := by
      linear_combination t00 - t 0 1 * h10 + (t 0 0 + 1) * h2
    have h3 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linear_combination h3 - h2
  have h11 : t 1 1 = 1 := by
    linear_combination htr - h00 - h2
  apply hT1
  apply Subtype.ext
  show t = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

theorem odd_orderOf_of_trace_ne_zero [Finite K] [CharP K 2] {A : SpecialLinearGroup (Fin 2) K}
    (htr : (A : Matrix (Fin 2) (Fin 2) K) 0 0 + (A : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0) :
    Odd (orderOf A) := by
  rcases Nat.even_or_odd (orderOf A) with ⟨k, hk⟩ | hodd
  · exfalso
    have hpos : 0 < orderOf A := orderOf_pos A
    have hk0 : k ≠ 0 := by omega
    apply htr
    refine trace_eq_zero_of_commute_involution (T := A ^ k) ?_ ?_ ?_
    · rw [← pow_add, ← hk, pow_orderOf_eq_one]
    · exact pow_ne_one_of_lt_orderOf hk0 (by omega)
    · exact (Commute.self_pow A k).eq
  · exact hodd

theorem coe_add_coe_inv (A : SpecialLinearGroup (Fin 2) K) :
    (A : Matrix (Fin 2) (Fin 2) K) + ((A⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) =
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0 + (A : Matrix (Fin 2) (Fin 2) K) 1 1) •
        (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hinv : ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(A : Matrix (Fin 2) (Fin 2) K) 1 1, -(A : Matrix (Fin 2) (Fin 2) K) 0 1;
        -(A : Matrix (Fin 2) (Fin 2) K) 1 0, (A : Matrix (Fin 2) (Fin 2) K) 0 0] := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, add_comm]

theorem trace_pow_two_pow_eq [CharP K 2] {A : SpecialLinearGroup (Fin 2) K} {N : ℕ}
    (h : A ^ (2 ^ N) = A) :
    ((A : Matrix (Fin 2) (Fin 2) K) 0 0 + (A : Matrix (Fin 2) (Fin 2) K) 1 1) ^ (2 ^ N) =
      (A : Matrix (Fin 2) (Fin 2) K) 0 0 + (A : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : Commute (A : Matrix (Fin 2) (Fin 2) K)
      ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have h1 : A * A⁻¹ = A⁻¹ * A := by rw [mul_inv_cancel, inv_mul_cancel]
    exact congrArg (fun X : SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) h1
  have hpow := add_pow_char_pow_of_commute 2 N hcomm
  have hM' : (A : Matrix (Fin 2) (Fin 2) K) ^ (2 ^ N) = A :=
    congrArg (fun X : SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) h
  have hMi' : ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ (2 ^ N) =
      ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have h1 : A⁻¹ ^ (2 ^ N) = A⁻¹ := by rw [inv_pow, h]
    exact congrArg (fun X : SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) h1
  rw [hM', hMi', coe_add_coe_inv, smul_pow, one_pow] at hpow
  have h00 := congrFun (congrFun hpow 0) 0
  simpa using h00

theorem mem_of_pow_eq_self [Finite K] (F₀ : Subfield K) {q : ℕ} (hq : Nat.card F₀ = q)
    (hq1 : 1 < q) {x : K} (hx : x ^ q = x) : x ∈ F₀ := by
  classical
  have := Fintype.ofFinite K
  have := Fintype.ofFinite F₀
  by_contra hxF
  set P : Polynomial K := Polynomial.X ^ q - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq1
  have hroot : ∀ y : K, y ^ q = y → y ∈ P.roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, hP, Polynomial.IsRoot,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hy, sub_self]
  have hF0 : ∀ y : F₀, (y : K) ^ q = y := by
    intro y
    have h1 : y ^ Fintype.card F₀ = y := FiniteField.pow_card y
    rw [← Nat.card_eq_fintype_card, hq] at h1
    exact congrArg Subtype.val h1
  set S : Finset K := insert x (Finset.univ.image (fun y : F₀ => (y : K))) with hS
  have hSsub : S ⊆ P.roots.toFinset := by
    intro y hy
    rw [hS, Finset.mem_insert, Finset.mem_image] at hy
    rcases hy with rfl | ⟨z, -, rfl⟩
    · exact hroot _ hx
    · exact hroot _ (hF0 z)
  have hcardS : S.card = q + 1 := by
    rw [hS, Finset.card_insert_of_notMem, Finset.card_image_of_injective _ Subtype.val_injective,
      Finset.card_univ, ← Nat.card_eq_fintype_card, hq]
    rw [Finset.mem_image]
    rintro ⟨z, -, hz⟩
    exact hxF (hz ▸ z.2)
  have h1 := Finset.card_le_card hSsub
  have h2 := Multiset.toFinset_card_le P.roots
  have h3 := Polynomial.card_roots' P
  have h4 : P.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq K hq1
  omega

theorem two_pow_mul_odd_inj {a b c d : ℕ} (hb : Odd b) (hd : Odd d)
    (h : 2 ^ a * b = 2 ^ c * d) : a = c ∧ b = d := by
  induction a generalizing c with
  | zero =>
    rcases c with _ | c
    · simpa using h
    · exfalso
      rw [pow_zero, one_mul, pow_succ, mul_comm (2 ^ c) 2, mul_assoc] at h
      exact (Nat.not_even_iff_odd.mpr hb) ⟨2 ^ c * d, by omega⟩
  | succ a ih =>
    rcases c with _ | c
    · exfalso
      rw [pow_zero, one_mul, pow_succ, mul_comm (2 ^ a) 2, mul_assoc] at h
      exact (Nat.not_even_iff_odd.mpr hd) ⟨2 ^ a * b, by omega⟩
    · rw [pow_succ, pow_succ, mul_comm (2 ^ a) 2, mul_comm (2 ^ c) 2, mul_assoc, mul_assoc] at h
      obtain ⟨h1, h2⟩ := ih (Nat.eq_of_mul_eq_mul_left (by norm_num) h)
      exact ⟨by rw [h1], h2⟩

theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  obtain ⟨c, hc⟩ := h2
  have hpos : 0 < 2 ^ k := by positivity
  exact ⟨c - 1, by omega⟩

theorem odd_two_pow_add_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k + 1) := by
  have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  obtain ⟨c, hc⟩ := h2
  exact ⟨c, by omega⟩

theorem center_slTwo_eq_bot [CharP K 2] :
    Subgroup.center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hrA⟩ := hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h2 : (r + 1) ^ 2 = 0 := by
      have h2' : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination hr + r * h2' + CharTwo.add_self_eq_zero (1 : K)
    have h3 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linear_combination h3 - CharTwo.add_self_eq_zero (1 : K)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

theorem card_psl2_charTwo (F : Type) [Field F] [Finite F] [CharP F 2] :
    Nat.card (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  have hc := center_slTwo_eq_bot (K := F)
  have e : CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F ≃* SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  rw [Nat.card_congr e.toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 2) (by norm_num)]
  simp

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
