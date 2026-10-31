
module

public import CFSG.Sporadic.ThSchreier.OrbitCheck819Base

public import CFSG.Sporadic.ThSchreier.Transporter
public import CFSG.Sporadic.ThSchreier.LocalOrbit
public meta import CFSG.Sporadic.ThSchreier.Transporter
public meta import CFSG.Sporadic.ThSchreier.LocalOrbit
public import CFSG.Sporadic.ThSchreier.OrbitCheck819Inputs
public import Certificates.Certificate2315
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

theorem isRows_rowsT : IsRows rowsT involT :=
  (isRows_rowsVInv.mul isRows_a).mul isRows_rowsV

theorem orbit_facts : orbitChecks orbTable = true :=
  Certificates.certificate2315

end CFSG.Sporadic.ThSchreier
