module

public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Sporadic.Schreier.M23Gens
public meta import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Schreier.M23Gens
public import CFSG.Sporadic.Schreier.M23PinnedInputs
public import Certificates.Certificate2197

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Monster.B.Mathieu

theorem mathieuCertificate_M23 : MathieuCertificateK "M23" = some m23Record :=
  Certificates.certificate2197.1

theorem m23_chain_check : m23Record.chain.check 23 = true :=
  Certificates.certificate2197.2.1

theorem m23_orbitSizes : m23Record.chain.orbitSizes 23 = [23, 22, 21, 20, 3, 16] :=
  Certificates.certificate2197.2.2.1

theorem m23_generators :
    m23Record.chain.generators = [imageList m23PermA, imageList m23PermB] :=
  Certificates.certificate2197.2.2.2

end CFSG.Sporadic.Schreier
