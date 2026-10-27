module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.RankThree.F2Mat

public section

namespace CFSG.RankThree.Native.F2

@[expose] noncomputable def vmulK (d m v M : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun k acc =>
    nIf(Nat.beq (Nat.land (Nat.shiftRight v k) (nat_lit 1)) (nat_lit 1),
      Nat.xor (fld(M, Nat.mul d k, m)) acc, acc)) d

@[expose] noncomputable def mulK (d m L A B : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun j acc =>
    Nat.xor (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A j) L) m)
      (Nat.mul (fld(B, Nat.mul d j, m)) L)) acc) d

theorem foldr_xor_init (g : ℕ → ℕ) (l : List ℕ) (a : ℕ) :
    l.foldr (fun j acc => g j ^^^ acc) a = l.foldr (fun j acc => g j ^^^ acc) 0 ^^^ a := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.foldr_cons, List.foldr_cons, ih, Nat.xor_assoc]

theorem rec_xor_eq_foldr (g : ℕ → ℕ) (t : ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => g j ^^^ acc) t =
      (List.range t).foldr (fun j acc => g j ^^^ acc) 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_xor_init, ← ih,
      Nat.xor_zero, Nat.xor_comm]

theorem land_mask_eq_row {d m : ℕ} (hm : m = 2 ^ d - 1) (M k : ℕ) :
    Nat.land (Nat.shiftRight M (Nat.mul d k)) m = row d M k := by
  subst hm
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem beq_bit (v k : ℕ) :
    Nat.beq (Nat.land (Nat.shiftRight v k) 1) 1 = v.testBit k := by
  have h : Nat.land (Nat.shiftRight v k) 1 = v / 2 ^ k % 2 := by
    change (v >>> k) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  cases Nat.mod_two_eq_zero_or_one (v / 2 ^ k) with
  | inl h0 => rw [h0]; rfl
  | inr h1 => rw [h1]; rfl

theorem vmulK_eq {d m : ℕ} (hm : m = 2 ^ d - 1) (v M : ℕ) : vmulK d m v M = vmul d v M := by
  have hstep : (fun k acc => nIf(Nat.beq (Nat.land (Nat.shiftRight v k) (nat_lit 1)) (nat_lit 1),
      Nat.xor (fld(M, Nat.mul d k, m)) acc, acc)) =
      fun k acc => (if v.testBit k then row d M k else 0) ^^^ acc := by
    funext k acc
    rw [beq_bit, land_mask_eq_row hm]
    cases v.testBit k
    · simp
    · rfl
  unfold vmulK
  rw [hstep, rec_xor_eq_foldr]
  unfold vmul
  congr 1
  funext k acc
  split <;> simp

theorem mulK_eq {d m L : ℕ} (hd : 0 < d) (hm : m = 2 ^ d - 1) (hL : L = lanes d) (A B : ℕ) :
    mulK d m L A B = mmul d A B := by
  rw [← mulL_eq hd]
  unfold mulK mulL
  subst hL
  have hstep : (fun j acc => Nat.xor (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A j) (lanes d))
      m) (Nat.mul (fld(B, Nat.mul d j, m)) (lanes d))) acc) = fun j acc =>
      ((((A >>> j) &&& lanes d) * (2 ^ d - 1)) &&& (row d B j * lanes d)) ^^^ acc := by
    funext j acc
    rw [land_mask_eq_row hm, hm]
    rfl
  rw [hstep, rec_xor_eq_foldr]

end CFSG.RankThree.Native.F2

end
