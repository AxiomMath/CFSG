
module

public import CFSG.Monster.B.TwoA.Co2Inv.KerEltsBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts

theorem xor_left_cancel' {a b c : ℕ} (h : a ^^^ b = a ^^^ c) : b = c := by
  have := congrArg (a ^^^ ·) h
  simpa only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] using this

theorem xor_four (a p b : ℕ) : a ^^^ p ^^^ b ^^^ p = a ^^^ b := by
  rw [Nat.xor_assoc a p b, Nat.xor_comm p b, ← Nat.xor_assoc, Nat.xor_assoc _ p p, Nat.xor_self,
    Nat.xor_zero]

theorem eq_zero_or_one {e : ℕ} (he : e < 2) : e = 0 ∨ e = 1 := by omega

theorem bvec4_eq_zero : ∀ l < 16, bvec 4 l = 0 → l = 0 := by decide +kernel

theorem natCard_vec : Nat.card (Multiplicative ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2))) = 256 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_fun, Nat.card_fin,
    Nat.card_zmod]
  norm_num

theorem bvec_dotProduct_par4 : ∀ l < 16, ∀ t < 16,
    bvec 4 l ⬝ᵥ bvec 4 t = ((par4 (l &&& t) : ℕ) : ZMod 2) := by
  decide +kernel

def AQ : Subgroup Qgrp := Agrp.subgroupOf Qgrp

end CFSG.Monster.B.TwoA.Co2Inv
