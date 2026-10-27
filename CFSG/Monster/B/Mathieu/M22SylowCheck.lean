module

public import Certificates.Certificate3158

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Sporadic.Mathieu

theorem m22_sylow_check :
    ∀ s ∈ m22Record.sylows,
      SylowFacts CFSG.Blueprint.NativeSporadic.M22 443520 [m22gA, m22gB] s :=
  Certificates.certificate3158.1

theorem m22_sylow_counts :
    m22Record.sylows.map (fun s => (s.prime, s.normalGeneration.length)) =
    [(2, 35), (3, 4), (5, 1), (7, 1), (11, 1)] :=
  Certificates.certificate3158.2

end CFSG.Monster.B.Mathieu
