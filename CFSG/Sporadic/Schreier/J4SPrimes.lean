
module

public import CFSG.Sporadic.Schreier.J4SKCentBase

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2.Native

@[expose] def bWord : List ℤ := [1, 2, 1, 2, 1, -2, 1, -2]

@[expose] def q5Cols : Array ℕ := #[762, 1484, 1751, 2015, 1841, 1743, 1791, 448, 1194, 85, 186]

@[expose] def w7 : List ℤ := [-2, 1, 2, -1, 2, -1, -2, -1, -2, 1]

@[expose] def q7Cols : Array ℕ := #[1544, 1315, 1338, 1566, 900, 328, 660, 100, 2034, 677, 128]

@[expose] def w23 : List ℤ := [1, 2]

@[expose] def q23Cols : Array ℕ := #[765, 1923, 1186, 894, 1804, 1730, 1475, 673, 1851, 901, 864]

@[expose] def B23 : Array ℕ := #[1, 765, 8, 894, 236, 1660, 820, 466, 214, 847, 991]

@[expose] def B23inv : Array ℕ := #[1, 797, 1868, 4, 986, 467, 849, 1498, 1740, 969, 1529]

@[expose] def polyCols (w : ℕ) : Array ℕ :=
  Array.ofFn (n := 11) fun i => app11 (powCols q23Cols i) w

@[expose] def Bounded (C : Array ℕ) : Prop := C.size = 11 ∧ ∀ j < 11, C[j]! < 2048

instance (C : Array ℕ) : Decidable (Bounded C) := inferInstanceAs (Decidable (_ ∧ _))

end CFSG.Sporadic.J4Schreier
