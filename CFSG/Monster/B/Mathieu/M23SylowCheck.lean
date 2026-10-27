module

public import Certificates.Certificate8051

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Sporadic.Schreier

theorem m23_sylow_check :
    ∀ s ∈ m23Record.sylows,
      SylowFacts CFSG.Blueprint.NativeSporadic.M23 10200960 [m23PermA, m23PermB] s :=
  Certificates.certificate8051.1

theorem m23_sylow_counts :
    m23Record.sylows.map (fun s => (s.prime, s.normalGeneration.length)) =
    [(2, 35), (3, 4), (5, 1), (7, 1), (11, 1), (23, 1)] :=
  Certificates.certificate8051.2

end CFSG.Monster.B.Mathieu
