module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFacts
public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
import Certificates.Kernel.StdOdd.C7A.ChecksP

public section

namespace Certificates

open CFSG.Monster.Existence.StdOdd.Cert in
theorem certificate6032 : CentFacts 7 141120 repWord7A (wordOfString "BABABBABAB")
    (fun i => [0, 1, 2, 3, 4, 5, 6].getD i 0)
    [(1, 5), (3, 4)] [(1, 5), (2, 3), (3, 4)] :=
  CFSG.KD.StdOdd.Cent.C7A.facts7A

end Certificates
