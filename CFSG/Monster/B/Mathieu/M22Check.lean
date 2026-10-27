module

public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Sporadic.Mathieu.M22
public meta import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Mathieu.M22
public import CFSG.Monster.B.Mathieu.M22CheckInputs
public import Certificates.Certificate3157

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Sporadic.Mathieu

theorem mathieuCertificate_M22 :
    MathieuCertificateK "M22" = some m22Record :=
  Certificates.certificate3157.1

theorem m22_chain_check : m22Record.chain.check 22 = true :=
  Certificates.certificate3157.2.1

theorem m22_orbitSizes :
    m22Record.chain.orbitSizes 22 = [22, 21, 20, 16, 3] :=
  Certificates.certificate3157.2.2.1

theorem m22_generators :
    m22Record.chain.generators = [imageList m22gA, imageList m22gB] :=
  Certificates.certificate3157.2.2.2

end CFSG.Monster.B.Mathieu
