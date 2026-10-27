module

public import CFSG.Sporadic.Co2Cert.Faithful
public import Certificates.Data.CFSGNative.Co2Smith.Words

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

abbrev K : Type := Blueprint.NativeSporadic.Co2

theorem val_val_mul (u v : K) : (u * v).val.val = u.val.val * v.val.val := rfl

theorem val_val_one : (1 : K).val.val = 1 := rfl

theorem eq_of_val_eq {u v : K} (h : u.val.val = v.val.val) : u = v :=
  Units.ext (Subtype.ext h)

structure Letters where
  elt : ℕ → K
  rows : Array (Array ℕ)
  val_eq : ∀ k < rows.size, (elt k).val.val = rowsMatrix 22 rows[k]!

@[expose] noncomputable def lWord (L : Letters) : List ℕ → K
  | [] => 1
  | k :: w => L.elt k * lWord L w

theorem lWord_val (L : Letters) : ∀ w : List ℕ, (∀ k ∈ w, k < L.rows.size) →
    (lWord L w).val.val = rowsMatrix 22 (Native.wRows L.rows w)
  | [], _ => by rw [lWord, val_val_one, Native.wRows, rowsMatrix_idRows]
  | k :: w, hw => by
    rw [lWord, val_val_mul, L.val_eq k (hw k List.mem_cons_self),
      lWord_val L w fun j hj => hw j (List.mem_cons_of_mem _ hj), Native.wRows,
      rowsMatrix_mulRows]

theorem lWord_append (L : Letters) (w w' : List ℕ) :
    lWord L (w ++ w') = lWord L w * lWord L w' := by
  induction w with
  | nil => rw [List.nil_append, lWord, one_mul]
  | cons k w ih => rw [List.cons_append, lWord, lWord, ih, mul_assoc]

theorem lWord_mem_closure (L : Letters) (S : Subgroup K) (hS : ∀ k, L.elt k ∈ S) :
    ∀ w : List ℕ, lWord L w ∈ S
  | [] => S.one_mem
  | k :: w => S.mul_mem (hS k) (lWord_mem_closure L S hS w)

theorem eq_of_rows {u v : K} {R R' : Array ℕ} (hu : u.val.val = rowsMatrix 22 R)
    (hv : v.val.val = rowsMatrix 22 R') (h : R = R') : u = v :=
  eq_of_val_eq (by rw [hu, hv, h])

theorem val_mulVec {u : K} {R : Array ℕ} (hu : u.val.val = rowsMatrix 22 R) (v : ℕ) :
    u.val.val *ᵥ toVecD 22 v = toVecD 22 (Native.colAct R v) := by
  rw [hu, rowsMatrix_mulVec, Native.colAct]

@[expose] noncomputable def seedLetters : Letters where
  elt k := if k = 0 then co2SeedA else co2SeedB
  rows := #[co2RowsA, co2RowsB]
  val_eq k hk := by
    rcases (show k = 0 ∨ k = 1 by simp at hk; omega) with rfl | rfl
    · change co2SeedA.val.val = _
      rw [co2SeedA_val, ← rowsMatrix_co2RowsA]
      rfl
    · change co2SeedB.val.val = _
      rw [co2SeedB_val, ← rowsMatrix_co2RowsB]
      rfl

end CFSG.Sporadic.Co2Smith
