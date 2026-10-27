
module

public import CFSG.Blueprint.MatrixSeedIdentification
public import Certificates.Data.CFSGNative.Co1.Data

@[expose] public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm.Native Matrix

abbrev dat : VecData := Native.co1Data

@[expose] def orbitOf (v n : ℕ) : VOrbit := vOrbitBFS 24 dat.colsA dat.colsB v n

@[expose] def orbitCheck (v n : ℕ) (others : List ℕ) : Bool :=
  let O := orbitOf v n
  let ls : Array Table := #[O.alpha, O.beta]
  let T := treeBFS n 0 ls #[0, 1]
  vOrbitOK 24 n dat.colsA dat.colsB O && O.pts[0]! == v && T.pts.size == n &&
    Perm.Native.treeOK n 0 T ls #[0, 1] && others.all fun w => !O.pts.contains w

end CFSG.Sporadic.Co1.Module
