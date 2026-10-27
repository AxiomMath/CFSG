module

public import Mathlib.GroupTheory.Perm.Sign

public section

namespace CFSG.Quasithin.H13.NPL

@[expose] def enc8 (d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ : ℕ) : ℕ :=
  d₀ + 8 * d₁ + 64 * d₂ + 512 * d₃ + 4096 * d₄ + 32768 * d₅ + 262144 * d₆ + 2097152 * d₇

@[expose] def dig (c i : ℕ) : ℕ := c / 8 ^ i % 8

@[expose] def encP (σ : Equiv.Perm (Fin 8)) : ℕ :=
  enc8 (σ 0).val (σ 1).val (σ 2).val (σ 3).val (σ 4).val (σ 5).val (σ 6).val (σ 7).val

@[expose] def mulC (a b : ℕ) : ℕ :=
  enc8 (dig a (dig b 0)) (dig a (dig b 1)) (dig a (dig b 2)) (dig a (dig b 3))
    (dig a (dig b 4)) (dig a (dig b 5)) (dig a (dig b 6)) (dig a (dig b 7))

@[expose] def idC (_ : Unit := ()) : ℕ := enc8 0 1 2 3 4 5 6 7

@[expose] def powC (c : ℕ) : ℕ → ℕ
  | 0 => idC ()
  | n + 1 => mulC (powC c n) c

@[expose] def S0gens (_ : Unit := ()) : List (Equiv.Perm (Fin 8)) :=
  [Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 4 5 * Equiv.swap 6 7, Equiv.swap 4 6 * Equiv.swap 5 7,
    Equiv.swap 0 1 * Equiv.swap 4 5,
    Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7]

@[expose] def S0codes (_ : Unit := ()) : List ℕ := (S0gens ()).map encP

end CFSG.Quasithin.H13.NPL

end
