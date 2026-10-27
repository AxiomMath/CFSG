module

public section

namespace CFSG.KGroups.U43

abbrev Word : Type := List (Nat × Bool)

@[expose] def wordA : Word :=
  [(1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
    (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false),
    (1, false), (0, false), (1, false), (1, false), (0, false), (1, true), (0, false),
    (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false),
    (0, false)]

@[expose] def wordS : Word :=
  [(1, false), (1, false), (0, false), (1, true), (0, false), (1, false), (1, false),
    (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
    (1, true), (1, true), (0, false), (1, false), (0, false), (1, true), (1, true), (0, false),
    (1, true), (0, false), (1, true), (1, true), (0, false)]

@[expose] def wordU : Word :=
  [(1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, false),
    (1, false), (1, false), (0, false), (1, false), (1, false), (1, false), (0, false),
    (1, true), (1, true), (0, false), (1, true), (0, false), (1, false), (1, false), (0, false),
    (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true),
    (1, true), (0, true), (1, true), (1, true)]

@[expose] def wordV : Word :=
  [(1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, true), (1, true),
    (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true),
    (0, true), (1, true), (1, true)]

@[expose] def wordPhi : Word :=
  [(1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (1, true),
    (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true),
    (1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true),
    (0, true), (1, false), (1, false)]

@[expose] def sylWord0 : Word :=
  [(1, true), (0, true), (1, false)]

@[expose] def sylWord1 : Word :=
  [(1, false), (1, false), (0, false), (1, false), (2, true), (1, true), (0, false), (1, false)]

@[expose] def sylWord2 : Word :=
  [(3, false), (2, false), (0, false), (1, false), (0, false), (2, false), (1, false)]

@[expose] def surjB : Word :=
  [(4, false), (2, false), (0, false), (4, false), (3, false), (4, true), (2, true), (1, true),
    (0, true), (2, true), (1, true), (3, false), (4, false), (0, false), (4, false)]

end CFSG.KGroups.U43
