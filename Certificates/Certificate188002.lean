module

public import Certificates.Certificate188002Base

import Certificates.Kernel.SchreierFam.C188002G

public section

open CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne

public section

namespace Certificates

open CertificateChecks.KernelSchreierFam.U38

open CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne

theorem certificate188002 : Cert188002Field ∧ Cert188002Points ∧ Cert188002Roots ∧ Cert188002Gens ∧ Cert188002Chain :=
  ⟨field, points, rootsSU.1, gens, chain⟩

namespace certificate188002

theorem field : Cert188002Field := certificate188002.1

theorem points : Cert188002Points := certificate188002.2.1

theorem roots : Cert188002Roots := certificate188002.2.2.1

theorem gens : Cert188002Gens := certificate188002.2.2.2.1

theorem chain : Cert188002Chain := certificate188002.2.2.2.2

end certificate188002

end Certificates