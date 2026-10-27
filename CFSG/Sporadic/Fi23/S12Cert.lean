module

public import CFSG.Sporadic.Fi23.InvCover
public import CFSG.Sporadic.Fi23.S12CertInputs
public import Certificates.Certificate10087
public meta import CFSG.Sporadic.Fi23.InvCert
public meta import Certificates.Data.CFSGNative.Fi23.Classes
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem s12_certificate : s12Certificate = true :=
  Certificates.certificate10087

end CFSG.Sporadic.Fi23
