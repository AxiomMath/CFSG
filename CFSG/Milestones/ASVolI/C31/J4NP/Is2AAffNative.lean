module

public import Certificates.Data.CFSGNative.J4Tree.Inv
public import CFSG.Sporadic.J4.QT2LocCntNative

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.J4Tree.Native

set_option compiler.extract_closed false

@[expose] def burnsideJ4NP_sextArr (_ : Unit := ()) : Array Bool := burnsideJ4NP_sextArrOf zMasks

@[expose] def burnsideJ4NP_affine2A (a : Code) : Bool :=
  burnsideJ4NP_affine2AWith (burnsideJ4NP_sextArr ()) a

end CFSG.ASVolI
