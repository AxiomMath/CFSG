module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFacts
public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
import Certificates.Kernel.StdOdd.C7B.ChecksP

public section

namespace Certificates

open CFSG.Monster.Existence.StdOdd.Cert in
theorem certificate6033 : CentFacts 7 1176 repWord7B (wordOfString "ABABBABBABABAB")
    (fun i => [0, 2, 4, 5, 3, 1, 6].getD i 0)
    [(2, 5), (3, 3)] [(2, 5), (1, 3), (3, 3)] :=
  CFSG.KD.StdOdd.Cent.C7B.facts7B

end Certificates
