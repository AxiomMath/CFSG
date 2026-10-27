module

public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Mathieu.M24
public import CFSG.Monster.B.Mathieu.M24CheckInputs
public import Certificates.Certificate3046

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Sporadic.Mathieu

theorem mathieuCertificate_M24 :
    MathieuCertificateK "M24" = some m24Record :=
  Certificates.certificate3046.1

theorem m24_chain_check : m24Record.chain.check 24 = true :=
  Certificates.certificate3046.2.1

theorem m24_orbitSizes :
    m24Record.chain.orbitSizes 24 = [24, 23, 22, 21, 20, 16, 3] :=
  Certificates.certificate3046.2.2.1

theorem m24_generators :
    m24Record.chain.generators = [imageList m24gA, imageList m24gB] :=
  Certificates.certificate3046.2.2.2

end CFSG.Monster.B.Mathieu
