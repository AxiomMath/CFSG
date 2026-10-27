
module

public import CFSG.Monster.B.Fischer.Fi22CertBase
public import CFSG.Monster.B.Fischer.Fi22SepData
public import Certificates.Data.CFSGNative.Fi22.Certificate
public meta import CFSG.Monster.B.Fischer.Fi22CertBase
public meta import CFSG.Monster.B.Fischer.Fi22SepData
public meta import Certificates.Data.CFSGNative.Fi22.Certificate
public meta import Certificates.Data.CFSGNative.Fi22Pinned.Forms

public section

namespace CFSG.Monster.B.Fischer

open CFSG.F3.Native CFSG.Monster.B.Fischer.Native

@[expose] def fi22SepMats : Array (Array V) :=
  fi22CentralizerIdx.toArray.map fun r => mul 77 fi22Bi (polarRows fi22FormsBytes (752 * r))

end CFSG.Monster.B.Fischer
