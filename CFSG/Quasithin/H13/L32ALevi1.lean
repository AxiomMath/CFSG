module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.Quasithin.H13.L32AC51a

public section

namespace CFSG.Quasithin.H13.L32A.C.Levi

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def toM (a : ℕ) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => if a.testBit (4 * (i : ℕ) + j) then 1 else 0

@[expose] def row (a i : ℕ) : ℕ := (a >>> (4 * i)) &&& 15

@[expose] def cb (r b : ℕ) : ℕ :=
  ((if r.testBit 0 then row b 0 else 0) ^^^ (if r.testBit 1 then row b 1 else 0)) ^^^
    ((if r.testBit 2 then row b 2 else 0) ^^^ (if r.testBit 3 then row b 3 else 0))

@[expose] def bmul (a b : ℕ) : ℕ :=
  cb (row a 0) b ||| (cb (row a 1) b <<< 4) ||| (cb (row a 2) b <<< 8) |||
    (cb (row a 3) b <<< 12)

@[expose] def idN : ℕ := 33825

@[expose] def perm16 (x : ℕ) : ℕ :=
  Nat.bit (x.testBit 15) <| Nat.bit (x.testBit 11) <| Nat.bit (x.testBit 7) <|
  Nat.bit (x.testBit 3) <| Nat.bit (x.testBit 14) <| Nat.bit (x.testBit 10) <|
  Nat.bit (x.testBit 6) <| Nat.bit (x.testBit 2) <| Nat.bit (x.testBit 13) <|
  Nat.bit (x.testBit 9) <| Nat.bit (x.testBit 5) <| Nat.bit (x.testBit 1) <|
  Nat.bit (x.testBit 12) <| Nat.bit (x.testBit 8) <| Nat.bit (x.testBit 4) <|
  Nat.bit (x.testBit 0) 0

@[expose] def uMemB (a : ℕ) : Bool :=
  !a.testBit 4 && !a.testBit 8 && !a.testBit 9 && !a.testBit 12 && !a.testBit 13 &&
    !a.testBit 14 && a.testBit 0 && a.testBit 5 && a.testBit 10 && a.testBit 15

theorem testBit_row (a i : ℕ) {j : ℕ} (hj : j < 4) :
    (row a i).testBit j = a.testBit (4 * i + j) := by
  have h15 : (15 : ℕ).testBit j = true := by interval_cases j <;> decide
  rw [row, Nat.testBit_land, Nat.testBit_shiftRight, h15, Bool.and_true]

theorem row_lt (a i : ℕ) : row a i < 2 ^ 4 :=
  lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem ite_row_lt (c : Bool) (a i : ℕ) : (if c then row a i else 0) < 2 ^ 4 := by
  split
  · exact row_lt a i
  · norm_num

theorem cb_lt (r b : ℕ) : cb r b < 2 ^ 4 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (ite_row_lt _ _ _) (ite_row_lt _ _ _))
    (Nat.xor_lt_two_pow (ite_row_lt _ _ _) (ite_row_lt _ _ _))

theorem testBit_ite (c : Bool) (x j : ℕ) :
    (if c then x else 0).testBit j = (c && x.testBit j) := by
  cases c <;> simp

theorem testBit_cb (r b : ℕ) {j : ℕ} (hj : j < 4) :
    (cb r b).testBit j = (((r.testBit 0 && b.testBit j) ^^ (r.testBit 1 && b.testBit (4 + j))) ^^
      ((r.testBit 2 && b.testBit (8 + j)) ^^ (r.testBit 3 && b.testBit (12 + j)))) := by
  simp only [cb, Nat.testBit_xor, testBit_ite, testBit_row _ _ hj]
  norm_num

theorem testBit_cb_high (r b : ℕ) {j : ℕ} (hj : 4 ≤ j) : (cb r b).testBit j = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (cb_lt r b) (Nat.pow_le_pow_right (by norm_num) hj))

theorem testBit_bmul (a b : ℕ) (i j : Fin 4) :
    (bmul a b).testBit (4 * (i : ℕ) + j) = (cb (row a i) b).testBit j := by
  fin_cases i <;> fin_cases j <;>
    simp (disch := decide) [bmul, Nat.testBit_shiftLeft, testBit_cb_high]

theorem bit_sum (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Bool) :
    (if ((x₀ && y₀) ^^ (x₁ && y₁)) ^^ ((x₂ && y₂) ^^ (x₃ && y₃)) then (1 : ZMod 2) else 0) =
      (if x₀ then 1 else 0) * (if y₀ then 1 else 0) +
        (if x₁ then 1 else 0) * (if y₁ then 1 else 0) +
        (if x₂ then 1 else 0) * (if y₂ then 1 else 0) +
          (if x₃ then 1 else 0) * (if y₃ then 1 else 0) := by
  revert x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃
  decide

theorem toM_bmul (a b : ℕ) : toM (bmul a b) = toM a * toM b := by
  ext i j
  have h0 := testBit_row a i (by norm_num : 0 < 4)
  have h1 := testBit_row a i (by norm_num : 1 < 4)
  have h2 := testBit_row a i (by norm_num : 2 < 4)
  have h3 := testBit_row a i (by norm_num : 3 < 4)
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  simp only [toM, Matrix.of_apply]
  rw [testBit_bmul, testBit_cb _ _ j.2, h0, h1, h2, h3, bit_sum]
  have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, e3, add_zero, mul_zero, zero_add, mul_one]

theorem toM_idN : toM idN = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toM_perm16 (x : ℕ) : toM (perm16 x) = ((toM x)ᵀ).submatrix Fin.revPerm Fin.revPerm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toM, perm16, Nat.testBit_bit_succ, Fin.rev]

theorem toM_eq_zero_iff (a : ℕ) (i j : Fin 4) :
    toM a i j = 0 ↔ a.testBit (4 * (i : ℕ) + j) = false := by
  simp only [toM, Matrix.of_apply]
  cases a.testBit (4 * (i : ℕ) + j) <;> decide

theorem toM_eq_one_iff (a : ℕ) (i j : Fin 4) :
    toM a i j = 1 ↔ a.testBit (4 * (i : ℕ) + j) = true := by
  simp only [toM, Matrix.of_apply]
  cases a.testBit (4 * (i : ℕ) + j) <;> decide

theorem uMemB_iff (a : ℕ) : uMemB a = true ↔
    (∀ i j : Fin 4, j < i → toM a i j = 0) ∧ ∀ i : Fin 4, toM a i i = 1 := by
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  constructor
  · intro h
    simp only [uMemB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h4, h8⟩, h9⟩, h12⟩, h13⟩, h14⟩, h0⟩, h5⟩, h10⟩, h15⟩ := h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [toM_eq_zero_iff]
      fin_cases i <;> fin_cases j <;> simp_all
    · rw [toM_eq_one_iff]
      fin_cases i <;> simp_all
  · rintro ⟨hl, hd⟩
    have h4 := (toM_eq_zero_iff a 1 0).mp (hl 1 0 (by decide))
    have h8 := (toM_eq_zero_iff a 2 0).mp (hl 2 0 (by decide))
    have h9 := (toM_eq_zero_iff a 2 1).mp (hl 2 1 (by decide))
    have h12 := (toM_eq_zero_iff a 3 0).mp (hl 3 0 (by decide))
    have h13 := (toM_eq_zero_iff a 3 1).mp (hl 3 1 (by decide))
    have h14 := (toM_eq_zero_iff a 3 2).mp (hl 3 2 (by decide))
    have h0 := (toM_eq_one_iff a 0 0).mp (hd 0)
    have h5 := (toM_eq_one_iff a 1 1).mp (hd 1)
    have h10 := (toM_eq_one_iff a 2 2).mp (hd 2)
    have h15 := (toM_eq_one_iff a 3 3).mp (hd 3)
    simp only [Fin.val_zero, v1, v2, v3] at h4 h8 h9 h12 h13 h14 h0 h5 h10 h15
    norm_num at h4 h8 h9 h12 h13 h14 h0 h5 h10 h15
    simp [uMemB, h4, h8, h9, h12, h13, h14, h0, h5, h10, h15]

theorem det_eq_one_of_mul {M N : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : M * N = 1) : M.det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h1
  exact BinaryParabolic.eq_one_of_ne_zero _ (left_ne_zero_of_mul_eq_one h1)

@[expose] noncomputable def sl (a a' : ℕ) : Lin.SLn 4 :=
  if h : toM a * toM a' = 1 then ⟨toM a, det_eq_one_of_mul h⟩ else 1

theorem coe_sl {a a' : ℕ} (h : bmul a a' = idN) : ((sl a a' : Lin.SLn 4) : Matrix (Fin 4) (Fin 4)
    (ZMod 2)) = toM a := by
  have h' : toM a * toM a' = 1 := by rw [← toM_bmul, h, toM_idN]
  simp [sl, h']

theorem mul_eq_idN_symm {a a' : ℕ} (h : bmul a a' = idN) : toM a' * toM a = 1 := by
  have h' : toM a * toM a' = 1 := by rw [← toM_bmul, h, toM_idN]
  rw [← Matrix.inv_eq_right_inv h']
  exact Matrix.nonsing_inv_mul _ (by rw [det_eq_one_of_mul h']; exact isUnit_one)

theorem sl_inv {a a' : ℕ} (h : bmul a a' = idN) (h' : bmul a' a = idN) :
    (sl a a')⁻¹ = sl a' a := by
  rw [inv_eq_iff_mul_eq_one]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_sl h,
    coe_sl h']
  rw [← toM_bmul, h, toM_idN]

theorem sl_mul {a a' b b' : ℕ} (ha : bmul a a' = idN) (hb : bmul b b' = idN)
    (hab : bmul (bmul a b) (bmul b' a') = idN) :
    sl (bmul a b) (bmul b' a') = sl a a' * sl b b' := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl hab, coe_sl ha, coe_sl hb, toM_bmul]

theorem mem_unitriangular_sl {a a' : ℕ} (h : bmul a a' = idN) :
    sl a a' ∈ unitriangular 4 (ZMod 2) ↔ uMemB a = true := by
  rw [uMemB_iff]
  show ((∀ i j : Fin 4, j < i → ((sl a a' : Lin.SLn 4) : Matrix _ _ (ZMod 2)) i j = 0) ∧
    ∀ i : Fin 4, ((sl a a' : Lin.SLn 4) : Matrix _ _ (ZMod 2)) i i = 1) ↔ _
  rw [coe_sl h]

theorem coe_graphFun_sl {a a' : ℕ} (h : bmul a a' = idN) (h' : bmul a' a = idN) :
    ((BinaryParabolic.graphFun (sl a a') : Lin.SLn 4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      toM (perm16 a') := by
  rw [BinaryParabolic.coe_graphFun, sl_inv h h', coe_sl h', toM_perm16]

end CFSG.Quasithin.H13.L32A.C.Levi
