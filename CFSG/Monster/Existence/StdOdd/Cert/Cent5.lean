module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFactsSound
public import Certificates.Certificate6031

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

theorem centFacts5 :
    CentFacts 5 100800 repWord5 (wordOfString "ABBABAB")
      (fun i => [0, 2, 3, 1, 4].getD i 0)
      [(2, 5), (1, 4)] [(2, 5), (1, 4)] :=
  Certificates.certificate6031

theorem card_centralizer_rep5 :
    Nat.card (Subgroup.centralizer ({rep5} : Set Rgrp)) = 100800 :=
  card_centralizer_of_centFacts orderOf_rep5 centFacts5

end CFSG.Monster.Existence.StdOdd.Cert
