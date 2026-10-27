module

public import Aesop.BuiltinRules

public section

namespace CFSG.Timmesfeld.Moufang.P3

@[expose] def wordA : List (Fin 5 × Bool) :=
  [(1, true), (3, true), (4, true), (1, true), (3, true), (2, true), (1, true), (0, true),
  (1, true), (3, true), (4, true), (1, true), (2, true), (3, true), (1, true), (2, true), (4, true),
  (1, true), (0, true), (1, true), (3, true), (4, true)]

@[expose] def wordB : List (Fin 5 × Bool) :=
  [(2, true), (3, true), (1, true), (0, true), (1, true), (2, true), (4, true), (1, true),
  (0, true), (3, true), (1, true), (0, true), (1, true), (2, true), (4, true), (1, true), (2, true),
  (4, true)]

@[expose] def conjX3 : List (Fin 5 × Bool) :=
  [(1, true), (0, true), (1, true), (4, true), (2, true), (1, true), (4, true), (3, true),
  (1, true), (2, true), (0, true), (1, true)]

@[expose] def conjX4 : List (Fin 5 × Bool) :=
  [(1, true), (0, true), (1, true), (3, true), (2, true), (1, true), (3, true), (4, true),
  (1, true), (2, true), (0, true), (1, true)]

end CFSG.Timmesfeld.Moufang.P3
