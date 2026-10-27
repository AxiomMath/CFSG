
module

public import CFSG.Sporadic.ThSchreier.AutCoreBase
public meta import CFSG.Sporadic.ThSchreier.RigidityBase

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates Equiv Equiv.Perm Matrix

@[expose] def dtWord : List ℕ :=
  [2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2]

@[expose] def dtCols : List ℕ := [100, 152, 247, 251, 184, 18, 228, 65]

end CFSG.Sporadic.ThSchreier
