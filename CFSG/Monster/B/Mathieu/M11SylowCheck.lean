module

public import Certificates.Certificate8050

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

theorem m11_sylow_check :
    ∀ s ∈ m11Record.sylows, SylowFacts CFSG.Blueprint.NativeSporadic.M11 7920 [m11gA, m11gB] s :=
  Certificates.certificate8050.1

theorem m11_sylow_counts :
    m11Record.sylows.map (fun s => (s.prime, s.normalGeneration.length)) =
    [(2, 5), (3, 4), (5, 1), (11, 1)] :=
  Certificates.certificate8050.2

end CFSG.Monster.B.Mathieu
