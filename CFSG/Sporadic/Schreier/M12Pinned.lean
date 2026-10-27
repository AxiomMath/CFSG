module

public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Schreier.M12PinnedInputs
public import Certificates.Certificate2194

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Monster.B.Mathieu CFSG.Sporadic.Mathieu

theorem mathieuCertificate_M12 : MathieuCertificateK "M12" = some m12Record :=
  Certificates.certificate2194.1

theorem m12_chain_check : m12Record.chain.check 12 = true :=
  Certificates.certificate2194.2.1

theorem m12_orbitSizes : m12Record.chain.orbitSizes 12 = [12, 11, 10, 9, 8] :=
  Certificates.certificate2194.2.2.1

theorem m12_generators : m12Record.chain.generators = [imageList m12gA, imageList m12gB] :=
  Certificates.certificate2194.2.2.2

end CFSG.Sporadic.Schreier
