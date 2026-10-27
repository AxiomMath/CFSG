module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFactsSound
public import Certificates.Certificate6033

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

theorem centFacts7B :
    CentFacts 7 1176 repWord7B (wordOfString "ABABBABBABABAB")
      (fun i => [0, 2, 4, 5, 3, 1, 6].getD i 0)
      [(2, 5), (3, 3)] [(2, 5), (1, 3), (3, 3)] :=
  Certificates.certificate6033

theorem card_centralizer_rep7B :
    Nat.card (Subgroup.centralizer ({rep7B} : Set Rgrp)) = 1176 :=
  card_centralizer_of_centFacts orderOf_rep7B centFacts7B

end CFSG.Monster.Existence.StdOdd.Cert
