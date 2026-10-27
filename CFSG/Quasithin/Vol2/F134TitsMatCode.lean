module

public import CFSG.Quasithin.Vol2.F134RuMatCode

public section

namespace CFSG.Quasithin.F134

open Matrix

@[expose] def rowBits26 (M : Matrix (Fin 26) (Fin 26) (ZMod 2)) (i : Fin 26) : ℕ :=
  ∑ k : Fin 26, (M i k).val * 2 ^ (k : ℕ)

@[expose] def matCode26 (M : Matrix (Fin 26) (Fin 26) (ZMod 2)) : ℕ :=
  ∑ i : Fin 26, rowBits26 M i * 2 ^ (26 * (i : ℕ))

theorem rowBits26_lt (M : Matrix (Fin 26) (Fin 26) (ZMod 2)) (i : Fin 26) :
    rowBits26 M i < 2 ^ 26 :=
  sum_lt_pow (b := 2) (fun k : Fin 26 => (M i k).val) (fun k => ZMod.val_lt (M i k))

theorem testBit_rowBits26 (M : Matrix (Fin 26) (Fin 26) (ZMod 2)) (i k : Fin 26) :
    (rowBits26 M i).testBit k = decide ((M i k).val = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, rowBits26,
    div_pow_mod_sum (by norm_num) _ (fun k' => ZMod.val_lt _) k]

theorem testBit_matCode26 (M : Matrix (Fin 26) (Fin 26) (ZMod 2)) (i k : Fin 26) :
    (matCode26 M).testBit (26 * (i : ℕ) + k) = decide ((M i k).val = 1) := by
  rw [matCode26, testBit_blockSum _ (rowBits26_lt M) i k.2, testBit_rowBits26]

theorem matCode26_injective : Function.Injective matCode26 := by
  intro M N h
  ext i k
  have e := testBit_matCode26 M i k
  rw [h, testBit_matCode26 N i k] at e
  rcases val_zmod2 (M i k) with h1 | h1 <;> rcases val_zmod2 (N i k) with h2 | h2
  · exact ZMod.val_injective _ (h1.trans h2.symm)
  · simp [h1, h2] at e
  · simp [h1, h2] at e
  · exact ZMod.val_injective _ (h1.trans h2.symm)

@[expose] def blk26 (x j : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 26 j)) 67108863

@[expose] def mask26 : ℕ := (2 ^ 676 - 1) / 67108863

@[expose] def col26 (x j : ℕ) : ℕ := Nat.land (Nat.shiftRight x j) mask26

@[expose] def mulF26 (x y : ℕ) : ℕ :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor
  (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor
  (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor 0 (Nat.mul (blk26 y 0) (col26 x 0))) (Nat.mul (blk26
  y 1) (col26 x 1))) (Nat.mul (blk26 y 2) (col26 x 2))) (Nat.mul (blk26 y 3) (col26 x 3))) (Nat.mul
  (blk26 y 4) (col26 x 4))) (Nat.mul (blk26 y 5) (col26 x 5))) (Nat.mul (blk26 y 6) (col26 x 6)))
  (Nat.mul (blk26 y 7) (col26 x 7))) (Nat.mul (blk26 y 8) (col26 x 8))) (Nat.mul (blk26 y 9) (col26
  x 9))) (Nat.mul (blk26 y 10) (col26 x 10))) (Nat.mul (blk26 y 11) (col26 x 11))) (Nat.mul (blk26
  y 12) (col26 x 12))) (Nat.mul (blk26 y 13) (col26 x 13))) (Nat.mul (blk26 y 14) (col26 x 14)))
  (Nat.mul (blk26 y 15) (col26 x 15))) (Nat.mul (blk26 y 16) (col26 x 16))) (Nat.mul (blk26 y 17)
  (col26 x 17))) (Nat.mul (blk26 y 18) (col26 x 18))) (Nat.mul (blk26 y 19) (col26 x 19))) (Nat.mul
  (blk26 y 20) (col26 x 20))) (Nat.mul (blk26 y 21) (col26 x 21))) (Nat.mul (blk26 y 22) (col26 x
  22))) (Nat.mul (blk26 y 23) (col26 x 23))) (Nat.mul (blk26 y 24) (col26 x 24))) (Nat.mul (blk26 y
  25) (col26 x 25))

theorem mulF26_eq (x y : ℕ) :
    mulF26 x y = xorSum (fun j => Nat.mul (blk26 y j) (col26 x j)) 26 := by
  simp only [xorSum]
  rfl

theorem mask26_eq : mask26 = ∑ i : Fin 26, 1 * 2 ^ (26 * (i : ℕ)) := by
  decide +kernel

theorem blk26_eq (x j : ℕ) : blk26 x j = x / (2 ^ 26) ^ j % 2 ^ 26 := digW_eq 26 x j

theorem blk26_matCode (M : Matrix (Fin 26) (Fin 26) (ZMod 2)) (j : Fin 26) :
    blk26 (matCode26 M) j = rowBits26 M j := by
  have h : matCode26 M = ∑ i : Fin 26, rowBits26 M i * (2 ^ 26) ^ (i : ℕ) := by
    unfold matCode26
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul]
  rw [blk26_eq, h]
  exact div_pow_mod_sum (by positivity) _ (rowBits26_lt M) j

theorem testBit_mask26 (i : Fin 26) (k : ℕ) (hk : k < 26) :
    mask26.testBit (26 * (i : ℕ) + k) = decide (k = 0) := by
  rw [mask26_eq, testBit_blockSum (fun _ : Fin 26 => 1) (fun _ => by norm_num) i hk]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · rw [Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow (by omega))]
    simp [hk0.ne']

theorem col26_matCode (M : Matrix (Fin 26) (Fin 26) (ZMod 2)) (j : Fin 26) :
    col26 (matCode26 M) j = ∑ i : Fin 26, (M i j).val * 2 ^ (26 * (i : ℕ)) := by
  have hf : ∀ i : Fin 26, (M i j).val < 2 ^ 26 :=
    fun i => (ZMod.val_lt (M i j)).trans (by norm_num)
  apply Nat.eq_of_testBit_eq
  intro p
  have hcol : col26 (matCode26 M) j = (matCode26 M >>> (j : ℕ)) &&& mask26 := rfl
  rw [hcol, Nat.testBit_land, Nat.testBit_shiftRight]
  rcases Nat.lt_or_ge p 676 with hp | hp
  · obtain ⟨i, k, hk, rfl⟩ : ∃ i : Fin 26, ∃ k : ℕ, k < 26 ∧ p = 26 * (i : ℕ) + k :=
      ⟨⟨p / 26, by omega⟩, p % 26, Nat.mod_lt _ (by norm_num), by simp [Nat.div_add_mod]⟩
    rw [testBit_mask26 i k hk, testBit_blockSum _ hf i hk]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [add_zero, add_comm, testBit_matCode26 M i j]
      rcases val_zmod2 (M i j) with h | h <;> simp [h]
    · have h1 : ((M i j).val).testBit k = false := by
        rcases val_zmod2 (M i j) with h | h <;> rw [h]
        · simp
        · exact Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow (by omega))
      rw [h1]
      simp [hk0.ne']
  · rw [testBit_blockSum_of_ge _ hf (by omega)]
    have : mask26.testBit p = false := by
      rw [mask26_eq]
      exact testBit_blockSum_of_ge (fun _ : Fin 26 => 1) (fun _ => by norm_num) (by omega)
    rw [this, Bool.and_false]

theorem term26_eq (M N : Matrix (Fin 26) (Fin 26) (ZMod 2)) (j : Fin 26) :
    Nat.mul (blk26 (matCode26 N) j) (col26 (matCode26 M) j) =
      ∑ i : Fin 26, ((M i j).val * rowBits26 N j) * 2 ^ (26 * (i : ℕ)) := by
  rw [blk26_matCode, col26_matCode, Nat.mul_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem term26_coeff_lt (M N : Matrix (Fin 26) (Fin 26) (ZMod 2)) (j i : Fin 26) :
    (M i j).val * rowBits26 N j < 2 ^ 26 := by
  rcases val_zmod2 (M i j) with h | h <;> rw [h]
  · simp
  · rw [one_mul]
    exact rowBits26_lt N j

theorem testBit_term26 (M N : Matrix (Fin 26) (Fin 26) (ZMod 2)) (j i : Fin 26) {k : ℕ}
    (hk : k < 26) :
    (Nat.mul (blk26 (matCode26 N) j) (col26 (matCode26 M) j)).testBit (26 * (i : ℕ) + k) =
      (decide ((M i j).val = 1) && (rowBits26 N j).testBit k) := by
  rw [term26_eq, testBit_blockSum _ (term26_coeff_lt M N j) i hk]
  rcases val_zmod2 (M i j) with h | h <;> rw [h] <;> simp

theorem val_mul_apply26 (M N : Matrix (Fin 26) (Fin 26) (ZMod 2)) (i k : Fin 26) :
    ((M * N) i k).val = (∑ j : Fin 26, (M i j).val * (N j k).val) % 2 := by
  have h : (M * N) i k = ((∑ j : Fin 26, (M i j).val * (N j k).val : ℕ) : ZMod 2) := by
    rw [Matrix.mul_apply]
    push_cast
    simp [ZMod.natCast_val]
  rw [h, ZMod.val_natCast]

theorem matCode26_mul (M N : Matrix (Fin 26) (Fin 26) (ZMod 2)) :
    matCode26 (M * N) = mulF26 (matCode26 M) (matCode26 N) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [mulF26_eq, testBit_xorSum, foldl_xor_eq]
  rcases Nat.lt_or_ge p 676 with hp | hp
  · obtain ⟨i, k, rfl⟩ : ∃ i k : Fin 26, p = 26 * (i : ℕ) + (k : ℕ) :=
      ⟨⟨p / 26, by omega⟩, ⟨p % 26, Nat.mod_lt _ (by norm_num)⟩, by simp [Nat.div_add_mod]⟩
    have hsum : ∑ j ∈ Finset.range 26, (if (Nat.mul (blk26 (matCode26 N) j)
        (col26 (matCode26 M) j)).testBit (26 * (i : ℕ) + (k : ℕ)) then 1 else 0) =
        ∑ j : Fin 26, (M i j).val * (N j k).val := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => if (Nat.mul (blk26 (matCode26 N) j)
        (col26 (matCode26 M) j)).testBit (26 * (i : ℕ) + (k : ℕ)) then 1 else 0) 26]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [testBit_term26 M N j i k.2, testBit_rowBits26]
      rcases val_zmod2 (M i j) with h1 | h1 <;> rcases val_zmod2 (N j k) with h2 | h2 <;>
        simp [h1, h2]
    rw [hsum, testBit_matCode26, val_mul_apply26]
  · have hfalse : ∀ j < 26, (Nat.mul (blk26 (matCode26 N) j)
        (col26 (matCode26 M) j)).testBit p = false := by
      intro j hj
      rw [show j = ((⟨j, hj⟩ : Fin 26) : ℕ) from rfl, term26_eq]
      exact testBit_blockSum_of_ge _ (term26_coeff_lt M N ⟨j, hj⟩) (by omega)
    have hsum : ∑ j ∈ Finset.range 26, (if (Nat.mul (blk26 (matCode26 N) j)
        (col26 (matCode26 M) j)).testBit p then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hfalse j (Finset.mem_range.mp hj)]; rfl
    rw [hsum, matCode26, testBit_blockSum_of_ge _ (rowBits26_lt (M * N)) (by omega)]
    rfl

@[expose] def glCode26 (u : GL (Fin 26) (ZMod 2)) : ℕ :=
  matCode26 (u : Matrix (Fin 26) (Fin 26) (ZMod 2))

theorem glCode26_mul (u v : GL (Fin 26) (ZMod 2)) :
    glCode26 (u * v) = mulF26 (glCode26 u) (glCode26 v) := by
  rw [glCode26, glCode26, glCode26, Units.val_mul, matCode26_mul]

theorem glCode26_injective : Function.Injective glCode26 :=
  fun _ _ h => Units.ext (matCode26_injective h)

@[expose] def mulBy26 (x y : ℕ) : ℕ := mulF26 y x

@[expose] def powC26 (one n x : ℕ) : ℕ := Nat.iterate (mulBy26 x) n one

theorem glCode26_pow (u : GL (Fin 26) (ZMod 2)) (n : ℕ) :
    glCode26 (u ^ n) = powC26 (glCode26 1) n (glCode26 u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, glCode26_mul, ih, powC26, powC26, Function.iterate_succ_apply']
    rfl

@[expose] def toM26 (x : ℕ) : Matrix (Fin 26) (Fin 26) (ZMod 2) :=
  Matrix.of fun i k => if x.testBit (26 * (i : ℕ) + (k : ℕ)) then 1 else 0

theorem matCode26_lt (M : Matrix (Fin 26) (Fin 26) (ZMod 2)) : matCode26 M < 2 ^ (26 * 26) :=
  blockSum_lt _ (rowBits26_lt M)

theorem testBit_eq_false_of_lt_pow_le {x m p : ℕ} (hx : x < 2 ^ m) (hp : m ≤ p) :
    x.testBit p = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right two_pos hp))

theorem matCode26_toM26 {x : ℕ} (hx : x < 2 ^ (26 * 26)) : matCode26 (toM26 x) = x := by
  apply Nat.eq_of_testBit_eq
  intro p
  rcases Nat.lt_or_ge p (26 * 26) with hp | hp
  · obtain ⟨i, k, rfl⟩ : ∃ i k : Fin 26, p = 26 * (i : ℕ) + (k : ℕ) :=
      ⟨⟨p / 26, by omega⟩, ⟨p % 26, Nat.mod_lt _ (by norm_num)⟩, by simp [Nat.div_add_mod]⟩
    rw [testBit_matCode26]
    simp only [toM26, Matrix.of_apply]
    by_cases h : x.testBit (26 * (i : ℕ) + (k : ℕ)) = true
    · simp only [h, ite_true]
      rfl
    · simp [h]
  · rw [testBit_eq_false_of_lt_pow_le (matCode26_lt _) hp, testBit_eq_false_of_lt_pow_le hx hp]

end CFSG.Quasithin.F134
