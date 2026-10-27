module

public import Mathlib.Data.ZMod.Basic

public section

namespace Certificates.OmegaSevenMax

abbrev V : Type := Fin 7 → ZMod 3

@[expose] def qV (x : V) : ZMod 3 :=
  x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 + x 4 * x 4 + x 5 * x 5 + x 6 * x 6 +
    2 * (x 0 * x 2 + x 1 * x 3 + x 2 * x 3 + x 3 * x 4 + x 4 * x 5 + x 5 * x 6)

@[expose] def polarV (x y : V) : ZMod 3 :=
  2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5 + x 6 * y 6) +
    2 * (x 0 * y 2 + x 2 * y 0 + x 1 * y 3 + x 3 * y 1 + x 2 * y 3 + x 3 * y 2 +
      x 3 * y 4 + x 4 * y 3 + x 4 * y 5 + x 5 * y 4 + x 5 * y 6 + x 6 * y 5)

@[expose] def rxV (u x : V) : V := x - polarV u x • u

@[expose] def encV (v : V) : ℕ :=
  (v 0).val + 3 * (v 1).val + 9 * (v 2).val + 27 * (v 3).val + 81 * (v 4).val +
    243 * (v 5).val + 729 * (v 6).val

@[expose] def decV (c : ℕ) : V := fun i => ((c / 3 ^ (i : ℕ) % 3 : ℕ) : ZMod 3)

end Certificates.OmegaSevenMax

end
