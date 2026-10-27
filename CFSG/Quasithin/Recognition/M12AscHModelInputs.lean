module

public import CFSG.Quasithin.Recognition.M12AscHPres
public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.Certificates.SubgroupEnumeration
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Quasithin

open CFSG.CosetTable

@[expose] def ascHRels : List (List (Fin 4 × Bool)) :=
  [[(0, true), (0, true), (0, true), (0, true)],
    [(2, true), (0, true), (2, false), (2, true), (0, true), (2, false), (0, false), (0, false)],
    [(2, true), (0, true), (2, false), (0, true), (2, true), (0, false), (2, false), (0, true)],
    [(0, true), (2, true), (0, true), (2, false), (2, true), (2, true), (0, false), (2, false), (2, false)],
    [(2, true), (2, true), (2, true)],
    [(1, true), (1, true), (1, true), (1, true)],
    [(1, true), (1, true), (0, false), (0, false)],
    [(2, true), (1, true), (2, false), (2, true), (1, true), (2, false), (0, false), (0, false)],
    [(2, true), (1, true), (2, false), (1, true), (2, true), (1, false), (2, false), (1, true)],
    [(1, true), (2, true), (1, true), (2, false), (2, true), (2, true), (1, false), (2, false), (2, false)],
    [(0, true), (1, true), (0, false), (1, false)],
    [(0, true), (2, true), (1, true), (2, false), (0, false), (2, true), (1, false), (2, false)],
    [(0, true), (2, true), (2, true), (1, true), (2, false), (2, false), (0, false), (2, true), (2, true), (1, false), (2, false), (2, false)],
    [(3, true), (3, true)],
    [(3, true), (2, true), (3, true), (2, true)],
    [(3, true), (0, true), (3, true), (2, true), (0, true), (2, false)],
    [(3, true), (1, true), (3, true), (2, true), (1, true), (2, false)]]

end CFSG.Quasithin
