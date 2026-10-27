module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFWreath

public section

namespace CFSG.StandardType.GGFF

open scoped MatrixGroups
open CFSG.RankThree.PartTwo.Sec4.RonanK429F

namespace N6

@[expose] def x0M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0]

@[expose] def r0M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 0, 0, 0;
    0, 1, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def r0'M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0;
    0, 1, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def r1M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 1, 0;
    0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def r1'M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 1, 0;
    0, 0, 0, 1, 0, 1]

theorem x0M_sq : x0M * x0M = 1 := by decide +kernel

theorem r0M_sq : r0M * r0M = 1 := by decide +kernel

theorem r0'M_sq : r0'M * r0'M = 1 := by decide +kernel

theorem r1M_sq : r1M * r1M = 1 := by decide +kernel

theorem r1'M_sq : r1'M * r1'M = 1 := by decide +kernel

@[expose] def x0 : SL(6, ZMod 2) := W6.mkSL6 x0M x0M x0M_sq

@[expose] def r : Fin 2 → SL(6, ZMod 2) := ![W6.mkSL6 r0M r0M r0M_sq, W6.mkSL6 r1M r1M r1M_sq]

@[expose] def r' : Fin 2 → SL(6, ZMod 2) :=
  ![W6.mkSL6 r0'M r0'M r0'M_sq, W6.mkSL6 r1'M r1'M r1'M_sq]

end N6

namespace N7

@[expose] def x0M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def r0M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def r0'M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def r1M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

@[expose] def r1'M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

theorem x0M_sq : x0M * x0M = 1 := by decide +kernel

theorem r0M_sq : r0M * r0M = 1 := by decide +kernel

theorem r0'M_sq : r0'M * r0'M = 1 := by decide +kernel

theorem r1M_sq : r1M * r1M = 1 := by decide +kernel

theorem r1'M_sq : r1'M * r1'M = 1 := by decide +kernel

@[expose] def x0 : SL(7, ZMod 2) := W7.mkSL7 x0M x0M x0M_sq

@[expose] def r : Fin 2 → SL(7, ZMod 2) := ![W7.mkSL7 r0M r0M r0M_sq, W7.mkSL7 r1M r1M r1M_sq]

@[expose] def r' : Fin 2 → SL(7, ZMod 2) :=
  ![W7.mkSL7 r0'M r0'M r0'M_sq, W7.mkSL7 r1'M r1'M r1'M_sq]

end N7

end CFSG.StandardType.GGFF

end
