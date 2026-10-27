module

public import CFSG.Quasithin.Vol2.F134PermCode
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.F134

open Matrix

theorem ofDigs_ofFn (b : ℕ) : ∀ {n : ℕ} (d : Fin n → ℕ),
    ofDigs b (List.ofFn d) = ∑ k, d k * b ^ (k : ℕ)
  | 0, d => by simp [ofDigs]
  | n + 1, d => by
    rw [List.ofFn_succ, ofDigs, ofDigs_ofFn, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring

theorem ofDigs_lt {b : ℕ} : ∀ (l : List ℕ), (∀ d ∈ l, d < b) → ofDigs b l < b ^ l.length
  | [], _ => by simp [ofDigs]
  | d :: l, hl => by
    have hd : d < b := hl d List.mem_cons_self
    have ih := ofDigs_lt l fun d' hd' => hl d' (List.mem_cons_of_mem _ hd')
    simp only [ofDigs, List.length_cons, pow_succ]
    nlinarith

theorem div_pow_mod_sum {b n : ℕ} (hb : 0 < b) (d : Fin n → ℕ) (hd : ∀ k, d k < b)
    (i : Fin n) : (∑ k, d k * b ^ (k : ℕ)) / b ^ (i : ℕ) % b = d i := by
  have hl : ∀ x ∈ List.ofFn d, x < b := by
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    exact hd k
  rw [← ofDigs_ofFn, div_pow_mod_ofDigs hb _ hl i (by simp)]
  simp

theorem sum_lt_pow {b n : ℕ} (d : Fin n → ℕ) (hd : ∀ k, d k < b) :
    ∑ k, d k * b ^ (k : ℕ) < b ^ n := by
  have hl : ∀ x ∈ List.ofFn d, x < b := by
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    exact hd k
  have := ofDigs_lt _ hl
  rwa [ofDigs_ofFn, List.length_ofFn] at this

@[expose] def fld14 (x p : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 8 p)) 255

@[expose] def blk14 (x j : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 112 j)) (2 ^ 112 - 1)

theorem fld14_eq (x p : ℕ) : fld14 x p = x / 256 ^ p % 256 := by
  have h : fld14 x p = digW 8 x p := rfl
  rw [h, digW_eq]
  norm_num

theorem blk14_eq (x j : ℕ) : blk14 x j = x / (2 ^ 112) ^ j % 2 ^ 112 := digW_eq 112 x j

@[expose] def rowC14 (x y i : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
  (Nat.add (Nat.add (Nat.add (0) (Nat.mul (fld14 x (Nat.add (Nat.mul 14 i) 0)) (blk14 y 0)))
  (Nat.mul (fld14 x (Nat.add (Nat.mul 14 i) 1)) (blk14 y 1))) (Nat.mul (fld14 x (Nat.add (Nat.mul 14
  i) 2)) (blk14 y 2))) (Nat.mul (fld14 x (Nat.add (Nat.mul 14 i) 3)) (blk14 y 3))) (Nat.mul (fld14 x
  (Nat.add (Nat.mul 14 i) 4)) (blk14 y 4))) (Nat.mul (fld14 x (Nat.add (Nat.mul 14 i) 5)) (blk14 y
  5))) (Nat.mul (fld14 x (Nat.add (Nat.mul 14 i) 6)) (blk14 y 6))) (Nat.mul (fld14 x (Nat.add
  (Nat.mul 14 i) 7)) (blk14 y 7))) (Nat.mul (fld14 x (Nat.add (Nat.mul 14 i) 8)) (blk14 y 8)))
  (Nat.mul (fld14 x (Nat.add (Nat.mul 14 i) 9)) (blk14 y 9))) (Nat.mul (fld14 x (Nat.add (Nat.mul 14
  i) 10)) (blk14 y 10))) (Nat.mul (fld14 x (Nat.add (Nat.mul 14 i) 11)) (blk14 y 11))) (Nat.mul
  (fld14 x (Nat.add (Nat.mul 14 i) 12)) (blk14 y 12))) (Nat.mul (fld14 x (Nat.add (Nat.mul 14 i)
  13)) (blk14 y 13))

@[expose] def red14 (r : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
  (Nat.add (Nat.add (Nat.add (0) (Nat.mul (Nat.mod (fld14 r 0) 5) (Nat.pow 256 0))) (Nat.mul
  (Nat.mod (fld14 r 1) 5) (Nat.pow 256 1))) (Nat.mul (Nat.mod (fld14 r 2) 5) (Nat.pow 256 2)))
  (Nat.mul (Nat.mod (fld14 r 3) 5) (Nat.pow 256 3))) (Nat.mul (Nat.mod (fld14 r 4) 5) (Nat.pow 256
  4))) (Nat.mul (Nat.mod (fld14 r 5) 5) (Nat.pow 256 5))) (Nat.mul (Nat.mod (fld14 r 6) 5) (Nat.pow
  256 6))) (Nat.mul (Nat.mod (fld14 r 7) 5) (Nat.pow 256 7))) (Nat.mul (Nat.mod (fld14 r 8) 5)
  (Nat.pow 256 8))) (Nat.mul (Nat.mod (fld14 r 9) 5) (Nat.pow 256 9))) (Nat.mul (Nat.mod (fld14 r
  10) 5) (Nat.pow 256 10))) (Nat.mul (Nat.mod (fld14 r 11) 5) (Nat.pow 256 11))) (Nat.mul (Nat.mod
  (fld14 r 12) 5) (Nat.pow 256 12))) (Nat.mul (Nat.mod (fld14 r 13) 5) (Nat.pow 256 13))

@[expose] def mul14 (x y : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
  (Nat.add (Nat.add (Nat.add (0) (Nat.mul (red14 (rowC14 x y 0)) (Nat.pow 256 (Nat.mul 14 0))))
  (Nat.mul (red14 (rowC14 x y 1)) (Nat.pow 256 (Nat.mul 14 1)))) (Nat.mul (red14 (rowC14 x y 2))
  (Nat.pow 256 (Nat.mul 14 2)))) (Nat.mul (red14 (rowC14 x y 3)) (Nat.pow 256 (Nat.mul 14 3))))
  (Nat.mul (red14 (rowC14 x y 4)) (Nat.pow 256 (Nat.mul 14 4)))) (Nat.mul (red14 (rowC14 x y 5))
  (Nat.pow 256 (Nat.mul 14 5)))) (Nat.mul (red14 (rowC14 x y 6)) (Nat.pow 256 (Nat.mul 14 6))))
  (Nat.mul (red14 (rowC14 x y 7)) (Nat.pow 256 (Nat.mul 14 7)))) (Nat.mul (red14 (rowC14 x y 8))
  (Nat.pow 256 (Nat.mul 14 8)))) (Nat.mul (red14 (rowC14 x y 9)) (Nat.pow 256 (Nat.mul 14 9))))
  (Nat.mul (red14 (rowC14 x y 10)) (Nat.pow 256 (Nat.mul 14 10)))) (Nat.mul (red14 (rowC14 x y 11))
  (Nat.pow 256 (Nat.mul 14 11)))) (Nat.mul (red14 (rowC14 x y 12)) (Nat.pow 256 (Nat.mul 14 12))))
  (Nat.mul (red14 (rowC14 x y 13)) (Nat.pow 256 (Nat.mul 14 13)))

@[expose] def rowVal14 (M : Matrix (Fin 14) (Fin 14) (ZMod 5)) (i : Fin 14) : ℕ :=
  ∑ k : Fin 14, (M i k).val * 256 ^ (k : ℕ)

@[expose] def matCode14 (M : Matrix (Fin 14) (Fin 14) (ZMod 5)) : ℕ :=
  ∑ i : Fin 14, rowVal14 M i * 256 ^ (14 * (i : ℕ))

theorem rowVal14_lt (M : Matrix (Fin 14) (Fin 14) (ZMod 5)) (i : Fin 14) :
    rowVal14 M i < 2 ^ 112 := by
  have := sum_lt_pow (b := 256) (fun k : Fin 14 => (M i k).val)
    (fun k => (ZMod.val_lt (M i k)).trans (by norm_num))
  rw [rowVal14]
  norm_num at this ⊢
  exact this

theorem blk14_matCode (M : Matrix (Fin 14) (Fin 14) (ZMod 5)) (j : Fin 14) :
    blk14 (matCode14 M) j = rowVal14 M j := by
  have h : matCode14 M = ∑ i : Fin 14, rowVal14 M i * (2 ^ 112) ^ (i : ℕ) := by
    unfold matCode14
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (2 : ℕ) ^ 112 = 256 ^ 14 by norm_num, ← pow_mul]
  rw [blk14_eq, h]
  exact div_pow_mod_sum (by positivity) _ (rowVal14_lt M) j

theorem fld14_matCode (M : Matrix (Fin 14) (Fin 14) (ZMod 5)) (i k : Fin 14) :
    fld14 (matCode14 M) (14 * (i : ℕ) + (k : ℕ)) = (M i k).val := by
  have hk := k.2
  have hpow : (256 : ℕ) ^ (14 * (i : ℕ) + (k : ℕ)) = (2 ^ 112) ^ (i : ℕ) * 256 ^ (k : ℕ) := by
    rw [pow_add, show (2 : ℕ) ^ 112 = 256 ^ 14 by norm_num, ← pow_mul]
  rw [fld14_eq, hpow, ← Nat.div_div_eq_div_mul]
  set y := matCode14 M / (2 ^ 112) ^ (i : ℕ) with hydef
  have hy : y % 2 ^ 112 = rowVal14 M i := (blk14_eq _ i).symm.trans (blk14_matCode M i)
  have h2 : (2 : ℕ) ^ 112 = 256 ^ (k : ℕ) * 256 ^ (14 - (k : ℕ)) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    norm_num
  have key : y / 256 ^ (k : ℕ) % 256 = y % 2 ^ 112 / 256 ^ (k : ℕ) % 256 := by
    rw [h2, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 256 (by omega))]
  rw [key, hy, rowVal14]
  exact div_pow_mod_sum (by norm_num) _ (fun k' => (ZMod.val_lt _).trans (by norm_num)) k

theorem rowC14_eq (x y i : ℕ) :
    rowC14 x y i = ∑ j ∈ Finset.range 14, fld14 x (14 * i + j) * blk14 y j := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rfl

theorem red14_eq (r : ℕ) : red14 r = ∑ k ∈ Finset.range 14, fld14 r k % 5 * 256 ^ k := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rfl

theorem mul14_eq (x y : ℕ) :
    mul14 x y = ∑ i ∈ Finset.range 14, red14 (rowC14 x y i) * 256 ^ (14 * i) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rfl

theorem val_mul_apply (M N : Matrix (Fin 14) (Fin 14) (ZMod 5)) (i k : Fin 14) :
    ((M * N) i k).val = (∑ j : Fin 14, (M i j).val * (N j k).val) % 5 := by
  have h : (M * N) i k = ((∑ j : Fin 14, (M i j).val * (N j k).val : ℕ) : ZMod 5) := by
    rw [Matrix.mul_apply]
    push_cast
    simp [ZMod.natCast_val]
  rw [h, ZMod.val_natCast]

theorem matCode14_mul (M N : Matrix (Fin 14) (Fin 14) (ZMod 5)) :
    matCode14 (M * N) = mul14 (matCode14 M) (matCode14 N) := by
  have hrow : ∀ i : Fin 14, rowC14 (matCode14 M) (matCode14 N) i =
      ∑ k : Fin 14, (∑ j : Fin 14, (M i j).val * (N j k).val) * 256 ^ (k : ℕ) := by
    intro i
    rw [rowC14_eq, ← Fin.sum_univ_eq_sum_range
      (fun j => fld14 (matCode14 M) (14 * (i : ℕ) + j) * blk14 (matCode14 N) j)]
    simp only [fld14_matCode, blk14_matCode, rowVal14, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hc : ∀ i k : Fin 14, ∑ j : Fin 14, (M i j).val * (N j k).val < 256 := by
    intro i k
    calc ∑ j : Fin 14, (M i j).val * (N j k).val ≤ ∑ _j : Fin 14, 16 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 := ZMod.val_lt (M i j)
          have h2 := ZMod.val_lt (N j k)
          have h3 : (M i j).val ≤ 4 := by omega
          have h4 : (N j k).val ≤ 4 := by omega
          calc (M i j).val * (N j k).val ≤ 4 * 4 := Nat.mul_le_mul h3 h4
            _ = 16 := by norm_num
      _ < 256 := by simp
  have hred : ∀ i : Fin 14,
      red14 (rowC14 (matCode14 M) (matCode14 N) i) = rowVal14 (M * N) i := by
    intro i
    rw [red14_eq, ← Fin.sum_univ_eq_sum_range
      (fun k => fld14 (rowC14 (matCode14 M) (matCode14 N) i) k % 5 * 256 ^ k), rowVal14]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrow i, fld14_eq, div_pow_mod_sum (by norm_num) _ (hc i) k, val_mul_apply]
  rw [mul14_eq, ← Fin.sum_univ_eq_sum_range
    (fun i => red14 (rowC14 (matCode14 M) (matCode14 N) i) * 256 ^ (14 * i)), matCode14]
  exact Finset.sum_congr rfl fun i _ => by rw [hred i]

theorem matCode14_injective : Function.Injective matCode14 := by
  intro M N h
  ext i k
  have e := fld14_matCode M i k
  rw [h, fld14_matCode N i k] at e
  exact ZMod.val_injective _ e.symm

@[expose] def glCode (u : GL (Fin 14) (ZMod 5)) : ℕ :=
  matCode14 (u : Matrix (Fin 14) (Fin 14) (ZMod 5))

theorem glCode_mul (u v : GL (Fin 14) (ZMod 5)) :
    glCode (u * v) = mul14 (glCode u) (glCode v) := by
  rw [glCode, glCode, glCode, Units.val_mul, matCode14_mul]

theorem glCode_injective : Function.Injective glCode :=
  fun _ _ h => Units.ext (matCode14_injective h)

@[expose] def mulBy14 (x y : ℕ) : ℕ := mul14 y x

@[expose] def powC14 (one n x : ℕ) : ℕ := Nat.iterate (mulBy14 x) n one

theorem glCode_pow (u : GL (Fin 14) (ZMod 5)) (n : ℕ) :
    glCode (u ^ n) = powC14 (glCode 1) n (glCode u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, glCode_mul, ih, powC14, powC14, Function.iterate_succ_apply']
    rfl

end CFSG.Quasithin.F134
