module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.StandardType.FrameRoute

abbrev F4 := GaloisField 2 2

theorem P9_F4_card : Nat.card F4 = 4 := by
  have h := GaloisField.card 2 2 (by norm_num)
  simpa using h

end CFSG.StandardType.FrameRoute
