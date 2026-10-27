module

public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import Certificates.Data.CFSGNative.Solomon.Co1T13

@[expose] public section

open CFSG.Sporadic.Co1Schreier

namespace Certificates

@[expose] noncomputable def y13Co1 : GL24 :=
  (dagG [A₁, A₂] (Solomon.Co1T13.dagWords13.map Native.decWord)).getD 3 1


end Certificates
