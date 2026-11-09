module

public import Certificates.Data.Kernel.VisFrame.Words

public section

namespace CFSG.KC.VisFrame

open CFSG.Monster.AxisCount.Native

def fwBit (v i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight v i) 1) 1

theorem fwBit_eq (v i : Nat) : fwBit v i = v.testBit i := by
  show Nat.beq ((v >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ i) with h | h <;> rw [h] <;> rfl

noncomputable def fwAct (rows : List Nat) (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Bool.rec acc (Nat.xor acc (rows.getD i 0)) (fwBit v i)) 24

theorem fwActGo_eq (rows : Array Nat) (v : Nat) : ∀ n acc, Cover.actGo rows v n acc =
    acc ^^^ Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Bool.rec acc (Nat.xor acc (rows.toList.getD i 0)) (fwBit v i)) n
  | 0, acc => (Nat.xor_zero acc).symm
  | n + 1, acc => by
    rw [Cover.actGo, fwActGo_eq rows v n]
    have hg : rows[n]! = rows.toList.getD n 0 := by
      by_cases h : n < rows.size
      · simp [List.getD_eq_getElem?_getD, h]
      · simp [List.getD_eq_getElem?_getD, h]
    show _ = acc ^^^ Bool.rec _ (_ ^^^ _) (fwBit v n)
    rw [fwBit_eq, hg]
    cases v.testBit n <;> simp [Nat.xor_assoc, Nat.xor_comm]

theorem fwActRows_eq (rows : Array Nat) (v : Nat) : Cover.actRows rows v = fwAct rows.toList v := by
  rw [Cover.actRows, fwActGo_eq, Nat.zero_xor]
  rfl

theorem frameWordsOK_eq_true : frameWordsOK = true := by
  simp only [frameWordsOK, frameWordOK.eq_unfold, frameGensOK, wordAct, frameWord, Cover.cvImg,
    fwActRows_eq]
  decide +kernel

end CFSG.KC.VisFrame

end
