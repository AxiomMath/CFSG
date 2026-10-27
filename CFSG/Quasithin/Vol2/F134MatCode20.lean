module

public import CFSG.Quasithin.Vol2.F134MatCode
public import Mathlib.Data.Nat.Bitwise
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Quasithin.F134

open Matrix

@[expose] def bit20 (x p : ℕ) : ℕ := Nat.land (Nat.shiftRight x p) 1

@[expose] def blk20 (x j : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 20 j)) 1048575

@[expose] def rowX20 (x y i : ℕ) : ℕ :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor
  (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (0) (Nat.mul
  (bit20 x (Nat.add (Nat.mul 20 i) 0)) (blk20 y 0))) (Nat.mul (bit20 x (Nat.add (Nat.mul 20 i) 1))
  (blk20 y 1))) (Nat.mul (bit20 x (Nat.add (Nat.mul 20 i) 2)) (blk20 y 2))) (Nat.mul (bit20 x
  (Nat.add (Nat.mul 20 i) 3)) (blk20 y 3))) (Nat.mul (bit20 x (Nat.add (Nat.mul 20 i) 4)) (blk20 y
  4))) (Nat.mul (bit20 x (Nat.add (Nat.mul 20 i) 5)) (blk20 y 5))) (Nat.mul (bit20 x (Nat.add
  (Nat.mul 20 i) 6)) (blk20 y 6))) (Nat.mul (bit20 x (Nat.add (Nat.mul 20 i) 7)) (blk20 y 7)))
  (Nat.mul (bit20 x (Nat.add (Nat.mul 20 i) 8)) (blk20 y 8))) (Nat.mul (bit20 x (Nat.add (Nat.mul 20
  i) 9)) (blk20 y 9))) (Nat.mul (bit20 x (Nat.add (Nat.mul 20 i) 10)) (blk20 y 10))) (Nat.mul (bit20
  x (Nat.add (Nat.mul 20 i) 11)) (blk20 y 11))) (Nat.mul (bit20 x (Nat.add (Nat.mul 20 i) 12))
  (blk20 y 12))) (Nat.mul (bit20 x (Nat.add (Nat.mul 20 i) 13)) (blk20 y 13))) (Nat.mul (bit20 x
  (Nat.add (Nat.mul 20 i) 14)) (blk20 y 14))) (Nat.mul (bit20 x (Nat.add (Nat.mul 20 i) 15)) (blk20
  y 15))) (Nat.mul (bit20 x (Nat.add (Nat.mul 20 i) 16)) (blk20 y 16))) (Nat.mul (bit20 x (Nat.add
  (Nat.mul 20 i) 17)) (blk20 y 17))) (Nat.mul (bit20 x (Nat.add (Nat.mul 20 i) 18)) (blk20 y 18)))
  (Nat.mul (bit20 x (Nat.add (Nat.mul 20 i) 19)) (blk20 y 19))

@[expose] def xorSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.xor (xorSum f n) (f n)

@[expose] def addSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.add (addSum f n) (f n)

@[expose] def mulX20 (x y : ℕ) : ℕ :=
  addSum (fun i => Nat.shiftLeft (rowX20 x y i) (Nat.mul 20 i)) 20

theorem addSum_eq (f : ℕ → ℕ) : ∀ n, addSum f n = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by rw [addSum, Finset.sum_range_succ, addSum_eq f n]; rfl

theorem bit20_eq (x p : ℕ) : bit20 x p = x / 2 ^ p % 2 := by
  have h : bit20 x p = (x >>> p) &&& 1 := rfl
  rw [h, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem blk20_eq (x j : ℕ) : blk20 x j = x / (2 ^ 20) ^ j % 2 ^ 20 := digW_eq 20 x j

@[expose] def rowBits20 (M : Matrix (Fin 20) (Fin 20) (ZMod 2)) (i : Fin 20) : ℕ :=
  ∑ k : Fin 20, (M i k).val * 2 ^ (k : ℕ)

@[expose] def matCode20 (M : Matrix (Fin 20) (Fin 20) (ZMod 2)) : ℕ :=
  ∑ i : Fin 20, rowBits20 M i * 2 ^ (20 * (i : ℕ))

theorem rowBits20_lt (M : Matrix (Fin 20) (Fin 20) (ZMod 2)) (i : Fin 20) :
    rowBits20 M i < 2 ^ 20 :=
  sum_lt_pow (b := 2) (fun k : Fin 20 => (M i k).val) (fun k => ZMod.val_lt (M i k))

theorem blk20_matCode (M : Matrix (Fin 20) (Fin 20) (ZMod 2)) (j : Fin 20) :
    blk20 (matCode20 M) j = rowBits20 M j := by
  have h : matCode20 M = ∑ i : Fin 20, rowBits20 M i * (2 ^ 20) ^ (i : ℕ) := by
    unfold matCode20
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul]
  rw [blk20_eq, h]
  exact div_pow_mod_sum (by positivity) _ (rowBits20_lt M) j

theorem bit20_matCode (M : Matrix (Fin 20) (Fin 20) (ZMod 2)) (i k : Fin 20) :
    bit20 (matCode20 M) (20 * (i : ℕ) + (k : ℕ)) = (M i k).val := by
  have hk := k.2
  have hpow : (2 : ℕ) ^ (20 * (i : ℕ) + (k : ℕ)) = (2 ^ 20) ^ (i : ℕ) * 2 ^ (k : ℕ) := by
    rw [pow_add, ← pow_mul]
  rw [bit20_eq, hpow, ← Nat.div_div_eq_div_mul]
  set y := matCode20 M / (2 ^ 20) ^ (i : ℕ) with hydef
  have hy : y % 2 ^ 20 = rowBits20 M i := (blk20_eq _ i).symm.trans (blk20_matCode M i)
  have h2 : (2 : ℕ) ^ 20 = 2 ^ (k : ℕ) * 2 ^ (20 - (k : ℕ)) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  have key : y / 2 ^ (k : ℕ) % 2 = y % 2 ^ 20 / 2 ^ (k : ℕ) % 2 := by
    rw [h2, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]
  rw [key, hy, rowBits20]
  exact div_pow_mod_sum (by norm_num) _ (fun k' => ZMod.val_lt _) k

theorem testBit_rowBits20 (M : Matrix (Fin 20) (Fin 20) (ZMod 2)) (i k : Fin 20) :
    (rowBits20 M i).testBit k = decide ((M i k).val = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, rowBits20,
    div_pow_mod_sum (by norm_num) _ (fun k' => ZMod.val_lt _) k]

theorem testBit_xorSum (f : ℕ → ℕ) (k : ℕ) : ∀ n : ℕ,
    (xorSum f n).testBit k = (List.range n).foldl (fun b j => xor b ((f j).testBit k)) false
  | 0 => by simp [xorSum]
  | n + 1 => by
    rw [xorSum, List.range_succ, List.foldl_append, ← testBit_xorSum f k n]
    simp [Nat.testBit_xor]

theorem rowX20_eq (x y i : ℕ) :
    rowX20 x y i = xorSum (fun j => bit20 x (20 * i + j) * blk20 y j) 20 := by
  simp only [rowX20, xorSum]
  rfl

theorem mulX20_eq (x y : ℕ) :
    mulX20 x y = ∑ i ∈ Finset.range 20, rowX20 x y i * 2 ^ (20 * i) := by
  rw [mulX20, addSum_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Nat.shiftLeft_eq _ _

theorem val_mul_apply20 (M N : Matrix (Fin 20) (Fin 20) (ZMod 2)) (i k : Fin 20) :
    ((M * N) i k).val = (∑ j : Fin 20, (M i j).val * (N j k).val) % 2 := by
  have h : (M * N) i k = ((∑ j : Fin 20, (M i j).val * (N j k).val : ℕ) : ZMod 2) := by
    rw [Matrix.mul_apply]
    push_cast
    simp [ZMod.natCast_val]
  rw [h, ZMod.val_natCast]

theorem foldl_xor_eq (g : ℕ → Bool) : ∀ n : ℕ,
    (List.range n).foldl (fun b j => xor b (g j)) false =
      decide ((∑ j ∈ Finset.range n, (if g j then 1 else 0)) % 2 = 1)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_xor_eq g n, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize (∑ j ∈ Finset.range n, (if g j then 1 else 0)) = S
    cases g n
    · simp
    · rcases Nat.mod_two_eq_zero_or_one S with h | h
      · have h' : (S + 1) % 2 = 1 := by omega
        simp [h, h']
      · have h' : (S + 1) % 2 = 0 := by omega
        simp [h, h']

theorem testBit_term20 (M N : Matrix (Fin 20) (Fin 20) (ZMod 2)) (i : Fin 20) (j : Fin 20)
    (k : Fin 20) :
    (bit20 (matCode20 M) (20 * (i : ℕ) + (j : ℕ)) * blk20 (matCode20 N) j).testBit k =
      (decide ((M i j).val = 1) && decide ((N j k).val = 1)) := by
  rw [bit20_matCode, blk20_matCode]
  have h1 : (M i j).val = 0 ∨ (M i j).val = 1 := by
    have := ZMod.val_lt (M i j)
    omega
  rcases h1 with h | h
  · rw [h, zero_mul]
    simp
  · rw [h, one_mul, testBit_rowBits20]
    simp

theorem term20_lt (M N : Matrix (Fin 20) (Fin 20) (ZMod 2)) (i : Fin 20) (j : Fin 20) :
    bit20 (matCode20 M) (20 * (i : ℕ) + (j : ℕ)) * blk20 (matCode20 N) j < 2 ^ 20 := by
  rw [bit20_matCode, blk20_matCode]
  have h1 := ZMod.val_lt (M i j)
  have h2 := rowBits20_lt N j
  calc (M i j).val * rowBits20 N j ≤ 1 * rowBits20 N j :=
        Nat.mul_le_mul_right _ (by simpa using Nat.lt_succ_iff.mp (by simpa using h1))
    _ < 2 ^ 20 := by rw [one_mul]; exact h2

theorem rowX20_matCode (M N : Matrix (Fin 20) (Fin 20) (ZMod 2)) (i : Fin 20) :
    rowX20 (matCode20 M) (matCode20 N) i = rowBits20 (M * N) i := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [rowX20_eq, testBit_xorSum, foldl_xor_eq]
  by_cases hk : k < 20
  · obtain ⟨k, rfl⟩ : ∃ k' : Fin 20, (k' : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
    have hsum : ∑ j ∈ Finset.range 20,
        (if ((bit20 (matCode20 M) (20 * (i : ℕ) + j) * blk20 (matCode20 N) j).testBit k)
          then 1 else 0) = ∑ j : Fin 20, (M i j).val * (N j k).val := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => if ((bit20 (matCode20 M) (20 * (i : ℕ) + j) *
        blk20 (matCode20 N) j).testBit k) then 1 else 0) 20]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [testBit_term20]
      have h1 : (M i j).val = 0 ∨ (M i j).val = 1 := by
        have := ZMod.val_lt (M i j)
        omega
      have h2 : (N j k).val = 0 ∨ (N j k).val = 1 := by
        have := ZMod.val_lt (N j k)
        omega
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]
    rw [hsum, testBit_rowBits20, val_mul_apply20]
  · have hk' : 20 ≤ k := by omega
    have hfalse : ∀ m : ℕ, m < 2 ^ 20 → m.testBit k = false := fun m hm =>
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hk'))
    rw [hfalse _ (rowBits20_lt _ _)]
    have hsum : ∑ j ∈ Finset.range 20,
        (if ((bit20 (matCode20 M) (20 * (i : ℕ) + j) * blk20 (matCode20 N) j).testBit k)
          then 1 else 0) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => if ((bit20 (matCode20 M) (20 * (i : ℕ) + j) *
        blk20 (matCode20 N) j).testBit k) then 1 else 0) 20]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hfalse _ (term20_lt M N i j)]
      rfl
    rw [hsum]
    rfl

theorem matCode20_mul (M N : Matrix (Fin 20) (Fin 20) (ZMod 2)) :
    matCode20 (M * N) = mulX20 (matCode20 M) (matCode20 N) := by
  rw [mulX20_eq, ← Fin.sum_univ_eq_sum_range
    (fun i => rowX20 (matCode20 M) (matCode20 N) i * 2 ^ (20 * i)), matCode20]
  exact Finset.sum_congr rfl fun i _ => by rw [rowX20_matCode]

theorem matCode20_injective : Function.Injective matCode20 := by
  intro M N h
  ext i k
  have e := bit20_matCode M i k
  rw [h, bit20_matCode N i k] at e
  exact ZMod.val_injective _ e.symm

@[expose] def glCode20 (u : GL (Fin 20) (ZMod 2)) : ℕ :=
  matCode20 (u : Matrix (Fin 20) (Fin 20) (ZMod 2))

theorem glCode20_mul (u v : GL (Fin 20) (ZMod 2)) :
    glCode20 (u * v) = mulX20 (glCode20 u) (glCode20 v) := by
  rw [glCode20, glCode20, glCode20, Units.val_mul, matCode20_mul]

theorem glCode20_injective : Function.Injective glCode20 :=
  fun _ _ h => Units.ext (matCode20_injective h)

@[expose] def mulBy20 (x y : ℕ) : ℕ := mulX20 y x

@[expose] def powC20 (one n x : ℕ) : ℕ := Nat.iterate (mulBy20 x) n one

theorem glCode20_pow (u : GL (Fin 20) (ZMod 2)) (n : ℕ) :
    glCode20 (u ^ n) = powC20 (glCode20 1) n (glCode20 u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, glCode20_mul, ih, powC20, powC20, Function.iterate_succ_apply']
    rfl

@[expose] def sq20 (x : ℕ) : ℕ := mulX20 x x

@[expose] def sqC20 (n x : ℕ) : ℕ := Nat.iterate sq20 n x

theorem glCode20_pow_two_pow (n : ℕ) : ∀ u : GL (Fin 20) (ZMod 2),
    glCode20 (u ^ 2 ^ n) = sqC20 n (glCode20 u) := by
  induction n with
  | zero => intro u; rw [pow_zero, pow_one]; rfl
  | succ n ih =>
    intro u
    rw [pow_succ', pow_mul, sq, ih, glCode20_mul, sqC20, sqC20, Function.iterate_succ_apply]
    rfl

end CFSG.Quasithin.F134
