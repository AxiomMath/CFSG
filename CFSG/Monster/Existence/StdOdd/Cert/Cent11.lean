module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFactsSound
public import Certificates.Certificate6027

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

theorem centFacts11 :
    CentFacts 11 66 repWord11 (wordOfString "BBABBABBABABABABABB")
      (fun i => [0, 4, 7, 3, 8, 1, 2, 5, 6, 9, 10].getD i 0)
      [(4, 5), (3, 3), (1, 4)] [(4, 5), (2, 3), (3, 3), (1, 4), (5, 4)] :=
  Certificates.certificate6027

theorem card_centralizer_rep11 :
    Nat.card (Subgroup.centralizer ({rep11} : Set Rgrp)) = 66 :=
  card_centralizer_of_centFacts orderOf_rep11 centFacts11

end CFSG.Monster.Existence.StdOdd.Cert
