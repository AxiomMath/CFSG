module

public import Init

public section

namespace CFSG.KC.BitT

@[expose] noncomputable def bitT (v j : Nat) : Bool := Nat.beq (Nat.land 1 (Nat.shiftRight v j)) 1

theorem bitT_eq (v j : Nat) : bitT v j = v.testBit j := by
  unfold bitT
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h : Nat.land 1 (Nat.shiftRight v j) = v / 2 ^ j % 2 := by
    show 1 &&& v >>> j = _
    rw [Nat.and_comm, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h]
  cases hh : Nat.beq (v / 2 ^ j % 2) 1
  · have := Nat.ne_of_beq_eq_false hh
    simp [this]
  · have := Nat.eq_of_beq_eq_true hh
    simp [this]

end CFSG.KC.BitT

end
