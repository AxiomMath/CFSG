module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFacts
public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
import Certificates.Kernel.StdOdd.C13.ChecksP

public section

namespace Certificates

open CFSG.Monster.Existence.StdOdd.Cert in
theorem certificate6028 : CentFacts 13 13 repWord13 (wordOfString "ABBABABBABBABABABABBABBAB")
    (fun i => [0, 1, 7, 6, 8, 2, 3, 4, 5, 9, 10, 11, 12].getD i 0)
    [(1, 5), (6, 5)] [(1, 5), (6, 5), (5, 3), (2, 4), (3, 4), (4, 4)] :=
  CFSG.KD.StdOdd.Cent.C13.facts13

end Certificates
