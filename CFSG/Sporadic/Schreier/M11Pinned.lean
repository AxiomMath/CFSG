module

public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Sporadic.Mathieu.M11
public meta import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Schreier.M11PinnedInputs
public import Certificates.Certificate2192

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Monster.B.Mathieu CFSG.Sporadic.Mathieu

theorem mathieuCertificate_M11 : MathieuCertificateK "M11" = some m11Record :=
  Certificates.certificate2192.1

theorem m11_chain_check : m11Record.chain.check 11 = true :=
  Certificates.certificate2192.2.1

theorem m11_orbitSizes : m11Record.chain.orbitSizes 11 = [11, 10, 9, 8] :=
  Certificates.certificate2192.2.2.1

theorem m11_generators : m11Record.chain.generators = [imageList m11gA, imageList m11gB] :=
  Certificates.certificate2192.2.2.2

end CFSG.Sporadic.Schreier
