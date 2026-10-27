
module

public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Monster.B

open CFSG.Blueprint

noncomputable abbrev genA₁ : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed1

noncomputable abbrev genA₂ : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed2

private theorem zmod_two_eq_one_of_pow {x : ZMod 2} {k : ℕ} (h : x ^ (k + 1) = 1) : x = 1 := by
  rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 by decide) x with rfl | rfl
  · rw [zero_pow (Nat.succ_ne_zero k)] at h
    exact absurd h (by decide)
  · rfl

end CFSG.Monster.B
