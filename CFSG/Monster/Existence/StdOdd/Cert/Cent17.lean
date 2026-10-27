module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFactsSound
public import Certificates.Certificate6029

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

theorem centFacts17 :
    CentFacts 17 17 repWord17 (wordOfString "BABABBABABABBABB")
      (fun i => [0, 7, 10, 3, 13, 6, 14, 1, 2, 4, 5, 8, 9, 11, 12, 15, 16].getD i 0)
      [(7, 5), (5, 4), (8, 4)] [(7, 5), (1, 3), (3, 3), (6, 3), (2, 4), (4, 4), (5, 4), (8, 4)] :=
  Certificates.certificate6029

theorem card_centralizer_rep17 :
    Nat.card (Subgroup.centralizer ({rep17} : Set Rgrp)) = 17 :=
  card_centralizer_of_centFacts orderOf_rep17 centFacts17

end CFSG.Monster.Existence.StdOdd.Cert
