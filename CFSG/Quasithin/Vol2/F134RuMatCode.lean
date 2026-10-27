module

public import CFSG.Quasithin.Vol2.F134MatCode20

public section

namespace CFSG.Quasithin.F134

open Matrix

theorem testBit_blockSum {w m : ℕ} (f : Fin m → ℕ) (hf : ∀ i, f i < 2 ^ w) (i : Fin m) {k : ℕ}
    (hk : k < w) : (∑ j, f j * 2 ^ (w * (j : ℕ))).testBit (w * (i : ℕ) + k) = (f i).testBit k := by
  have hsum : ∑ j, f j * 2 ^ (w * (j : ℕ)) = ∑ j, f j * (2 ^ w) ^ (j : ℕ) :=
    Finset.sum_congr rfl fun j _ => by rw [← pow_mul]
  rw [hsum, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  congr 1
  set z := ∑ j, f j * (2 ^ w) ^ (j : ℕ)
  have hz : z / (2 ^ w) ^ (i : ℕ) % 2 ^ w = f i := div_pow_mod_sum (by positivity) f hf i
  have hpow : (2 : ℕ) ^ (w * (i : ℕ) + k) = (2 ^ w) ^ (i : ℕ) * 2 ^ k := by
    rw [pow_add, ← pow_mul]
  rw [hpow, ← Nat.div_div_eq_div_mul]
  set y := z / (2 ^ w) ^ (i : ℕ)
  have h2 : (2 : ℕ) ^ w = 2 ^ k * 2 ^ (w - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk.le]
  have key : y / 2 ^ k % 2 = y % 2 ^ w / 2 ^ k % 2 := by
    rw [h2, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]
  rw [key, hz]

theorem blockSum_lt {w m : ℕ} (f : Fin m → ℕ) (hf : ∀ i, f i < 2 ^ w) :
    ∑ j, f j * 2 ^ (w * (j : ℕ)) < 2 ^ (w * m) := by
  have hsum : ∑ j, f j * 2 ^ (w * (j : ℕ)) = ∑ j, f j * (2 ^ w) ^ (j : ℕ) :=
    Finset.sum_congr rfl fun j _ => by rw [← pow_mul]
  rw [hsum, pow_mul]
  exact sum_lt_pow f hf

theorem testBit_blockSum_of_ge {w m : ℕ} (f : Fin m → ℕ) (hf : ∀ i, f i < 2 ^ w) {p : ℕ}
    (hp : w * m ≤ p) : (∑ j, f j * 2 ^ (w * (j : ℕ))).testBit p = false :=
  Nat.testBit_eq_false_of_lt ((blockSum_lt f hf).trans_le (Nat.pow_le_pow_right (by norm_num) hp))

@[expose] def rowBits28 (M : Matrix (Fin 28) (Fin 28) (ZMod 2)) (i : Fin 28) : ℕ :=
  ∑ k : Fin 28, (M i k).val * 2 ^ (k : ℕ)

@[expose] def matCode28 (M : Matrix (Fin 28) (Fin 28) (ZMod 2)) : ℕ :=
  ∑ i : Fin 28, rowBits28 M i * 2 ^ (28 * (i : ℕ))

theorem val_zmod2 (a : ZMod 2) : a.val = 0 ∨ a.val = 1 := by
  have := ZMod.val_lt a
  omega

theorem rowBits28_lt (M : Matrix (Fin 28) (Fin 28) (ZMod 2)) (i : Fin 28) :
    rowBits28 M i < 2 ^ 28 :=
  sum_lt_pow (b := 2) (fun k : Fin 28 => (M i k).val) (fun k => ZMod.val_lt (M i k))

theorem testBit_rowBits28 (M : Matrix (Fin 28) (Fin 28) (ZMod 2)) (i k : Fin 28) :
    (rowBits28 M i).testBit k = decide ((M i k).val = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, rowBits28,
    div_pow_mod_sum (by norm_num) _ (fun k' => ZMod.val_lt _) k]

theorem testBit_matCode28 (M : Matrix (Fin 28) (Fin 28) (ZMod 2)) (i k : Fin 28) :
    (matCode28 M).testBit (28 * (i : ℕ) + k) = decide ((M i k).val = 1) := by
  rw [matCode28, testBit_blockSum _ (rowBits28_lt M) i k.2, testBit_rowBits28]

theorem matCode28_injective : Function.Injective matCode28 := by
  intro M N h
  ext i k
  have e := testBit_matCode28 M i k
  rw [h, testBit_matCode28 N i k] at e
  rcases val_zmod2 (M i k) with h1 | h1 <;> rcases val_zmod2 (N i k) with h2 | h2
  · exact ZMod.val_injective _ (h1.trans h2.symm)
  · simp [h1, h2] at e
  · simp [h1, h2] at e
  · exact ZMod.val_injective _ (h1.trans h2.symm)

@[expose] def blk28 (x j : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 28 j)) 268435455

@[expose] def mask28 : ℕ := (2 ^ 784 - 1) / 268435455

@[expose] def col28 (x j : ℕ) : ℕ := Nat.land (Nat.shiftRight x j) mask28

@[expose] def mulF28 (x y : ℕ) : ℕ :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor
  (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor
  (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor 0 (Nat.mul (blk28 y 0) (col28 x 0)))
  (Nat.mul (blk28 y 1) (col28 x 1))) (Nat.mul (blk28 y 2) (col28 x 2))) (Nat.mul (blk28 y 3) (col28
  x 3))) (Nat.mul (blk28 y 4) (col28 x 4))) (Nat.mul (blk28 y 5) (col28 x 5))) (Nat.mul (blk28 y 6)
  (col28 x 6))) (Nat.mul (blk28 y 7) (col28 x 7))) (Nat.mul (blk28 y 8) (col28 x 8))) (Nat.mul
  (blk28 y 9) (col28 x 9))) (Nat.mul (blk28 y 10) (col28 x 10))) (Nat.mul (blk28 y 11) (col28 x
  11))) (Nat.mul (blk28 y 12) (col28 x 12))) (Nat.mul (blk28 y 13) (col28 x 13))) (Nat.mul (blk28 y
  14) (col28 x 14))) (Nat.mul (blk28 y 15) (col28 x 15))) (Nat.mul (blk28 y 16) (col28 x 16)))
  (Nat.mul (blk28 y 17) (col28 x 17))) (Nat.mul (blk28 y 18) (col28 x 18))) (Nat.mul (blk28 y 19)
  (col28 x 19))) (Nat.mul (blk28 y 20) (col28 x 20))) (Nat.mul (blk28 y 21) (col28 x 21))) (Nat.mul
  (blk28 y 22) (col28 x 22))) (Nat.mul (blk28 y 23) (col28 x 23))) (Nat.mul (blk28 y 24) (col28 x
  24))) (Nat.mul (blk28 y 25) (col28 x 25))) (Nat.mul (blk28 y 26) (col28 x 26))) (Nat.mul (blk28 y
  27) (col28 x 27))

theorem mulF28_eq (x y : ℕ) :
    mulF28 x y = xorSum (fun j => Nat.mul (blk28 y j) (col28 x j)) 28 := by
  simp only [xorSum]
  rfl

theorem mask28_eq : mask28 = ∑ i : Fin 28, 1 * 2 ^ (28 * (i : ℕ)) := by
  decide +kernel

theorem blk28_eq (x j : ℕ) : blk28 x j = x / (2 ^ 28) ^ j % 2 ^ 28 := digW_eq 28 x j

theorem blk28_matCode (M : Matrix (Fin 28) (Fin 28) (ZMod 2)) (j : Fin 28) :
    blk28 (matCode28 M) j = rowBits28 M j := by
  have h : matCode28 M = ∑ i : Fin 28, rowBits28 M i * (2 ^ 28) ^ (i : ℕ) := by
    unfold matCode28
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul]
  rw [blk28_eq, h]
  exact div_pow_mod_sum (by positivity) _ (rowBits28_lt M) j

theorem testBit_mask28 (i : Fin 28) (k : ℕ) (hk : k < 28) :
    mask28.testBit (28 * (i : ℕ) + k) = decide (k = 0) := by
  rw [mask28_eq, testBit_blockSum (fun _ : Fin 28 => 1) (fun _ => by norm_num) i hk]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · rw [Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow (by omega))]
    simp [hk0.ne']

theorem col28_matCode (M : Matrix (Fin 28) (Fin 28) (ZMod 2)) (j : Fin 28) :
    col28 (matCode28 M) j = ∑ i : Fin 28, (M i j).val * 2 ^ (28 * (i : ℕ)) := by
  have hf : ∀ i : Fin 28, (M i j).val < 2 ^ 28 :=
    fun i => (ZMod.val_lt (M i j)).trans (by norm_num)
  apply Nat.eq_of_testBit_eq
  intro p
  have hcol : col28 (matCode28 M) j = (matCode28 M >>> (j : ℕ)) &&& mask28 := rfl
  rw [hcol, Nat.testBit_land, Nat.testBit_shiftRight]
  rcases Nat.lt_or_ge p 784 with hp | hp
  · obtain ⟨i, k, hk, rfl⟩ : ∃ i : Fin 28, ∃ k : ℕ, k < 28 ∧ p = 28 * (i : ℕ) + k :=
      ⟨⟨p / 28, by omega⟩, p % 28, Nat.mod_lt _ (by norm_num), by simp [Nat.div_add_mod]⟩
    rw [testBit_mask28 i k hk, testBit_blockSum _ hf i hk]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [add_zero, add_comm, testBit_matCode28 M i j]
      rcases val_zmod2 (M i j) with h | h <;> simp [h]
    · have h1 : ((M i j).val).testBit k = false := by
        rcases val_zmod2 (M i j) with h | h <;> rw [h]
        · simp
        · exact Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow (by omega))
      rw [h1]
      simp [hk0.ne']
  · rw [testBit_blockSum_of_ge _ hf (by omega)]
    have : mask28.testBit p = false := by
      rw [mask28_eq]
      exact testBit_blockSum_of_ge (fun _ : Fin 28 => 1) (fun _ => by norm_num) (by omega)
    rw [this, Bool.and_false]

theorem term28_eq (M N : Matrix (Fin 28) (Fin 28) (ZMod 2)) (j : Fin 28) :
    Nat.mul (blk28 (matCode28 N) j) (col28 (matCode28 M) j) =
      ∑ i : Fin 28, ((M i j).val * rowBits28 N j) * 2 ^ (28 * (i : ℕ)) := by
  rw [blk28_matCode, col28_matCode, Nat.mul_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem term28_coeff_lt (M N : Matrix (Fin 28) (Fin 28) (ZMod 2)) (j i : Fin 28) :
    (M i j).val * rowBits28 N j < 2 ^ 28 := by
  rcases val_zmod2 (M i j) with h | h <;> rw [h]
  · simp
  · rw [one_mul]
    exact rowBits28_lt N j

theorem testBit_term28 (M N : Matrix (Fin 28) (Fin 28) (ZMod 2)) (j i : Fin 28) {k : ℕ}
    (hk : k < 28) :
    (Nat.mul (blk28 (matCode28 N) j) (col28 (matCode28 M) j)).testBit (28 * (i : ℕ) + k) =
      (decide ((M i j).val = 1) && (rowBits28 N j).testBit k) := by
  rw [term28_eq, testBit_blockSum _ (term28_coeff_lt M N j) i hk]
  rcases val_zmod2 (M i j) with h | h <;> rw [h] <;> simp

theorem val_mul_apply28 (M N : Matrix (Fin 28) (Fin 28) (ZMod 2)) (i k : Fin 28) :
    ((M * N) i k).val = (∑ j : Fin 28, (M i j).val * (N j k).val) % 2 := by
  have h : (M * N) i k = ((∑ j : Fin 28, (M i j).val * (N j k).val : ℕ) : ZMod 2) := by
    rw [Matrix.mul_apply]
    push_cast
    simp [ZMod.natCast_val]
  rw [h, ZMod.val_natCast]

theorem matCode28_mul (M N : Matrix (Fin 28) (Fin 28) (ZMod 2)) :
    matCode28 (M * N) = mulF28 (matCode28 M) (matCode28 N) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [mulF28_eq, testBit_xorSum, foldl_xor_eq]
  rcases Nat.lt_or_ge p 784 with hp | hp
  · obtain ⟨i, k, rfl⟩ : ∃ i k : Fin 28, p = 28 * (i : ℕ) + (k : ℕ) :=
      ⟨⟨p / 28, by omega⟩, ⟨p % 28, Nat.mod_lt _ (by norm_num)⟩, by simp [Nat.div_add_mod]⟩
    have hsum : ∑ j ∈ Finset.range 28, (if (Nat.mul (blk28 (matCode28 N) j)
        (col28 (matCode28 M) j)).testBit (28 * (i : ℕ) + (k : ℕ)) then 1 else 0) =
        ∑ j : Fin 28, (M i j).val * (N j k).val := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => if (Nat.mul (blk28 (matCode28 N) j)
        (col28 (matCode28 M) j)).testBit (28 * (i : ℕ) + (k : ℕ)) then 1 else 0) 28]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [testBit_term28 M N j i k.2, testBit_rowBits28]
      rcases val_zmod2 (M i j) with h1 | h1 <;> rcases val_zmod2 (N j k) with h2 | h2 <;>
        simp [h1, h2]
    rw [hsum, testBit_matCode28, val_mul_apply28]
  · have hfalse : ∀ j < 28, (Nat.mul (blk28 (matCode28 N) j)
        (col28 (matCode28 M) j)).testBit p = false := by
      intro j hj
      rw [show j = ((⟨j, hj⟩ : Fin 28) : ℕ) from rfl, term28_eq]
      exact testBit_blockSum_of_ge _ (term28_coeff_lt M N ⟨j, hj⟩) (by omega)
    have hsum : ∑ j ∈ Finset.range 28, (if (Nat.mul (blk28 (matCode28 N) j)
        (col28 (matCode28 M) j)).testBit p then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hfalse j (Finset.mem_range.mp hj)]; rfl
    rw [hsum, matCode28, testBit_blockSum_of_ge _ (rowBits28_lt (M * N)) (by omega)]
    rfl

@[expose] def glCode28 (u : GL (Fin 28) (ZMod 2)) : ℕ :=
  matCode28 (u : Matrix (Fin 28) (Fin 28) (ZMod 2))

theorem glCode28_mul (u v : GL (Fin 28) (ZMod 2)) :
    glCode28 (u * v) = mulF28 (glCode28 u) (glCode28 v) := by
  rw [glCode28, glCode28, glCode28, Units.val_mul, matCode28_mul]

theorem glCode28_injective : Function.Injective glCode28 :=
  fun _ _ h => Units.ext (matCode28_injective h)

@[expose] def mulBy28 (x y : ℕ) : ℕ := mulF28 y x

@[expose] def powC28 (one n x : ℕ) : ℕ := Nat.iterate (mulBy28 x) n one

theorem glCode28_pow (u : GL (Fin 28) (ZMod 2)) (n : ℕ) :
    glCode28 (u ^ n) = powC28 (glCode28 1) n (glCode28 u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, glCode28_mul, ih, powC28, powC28, Function.iterate_succ_apply']
    rfl

end CFSG.Quasithin.F134
