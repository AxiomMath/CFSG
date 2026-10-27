module

public import Certificates.Certificate799601

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG.LieType.Chevalley CFSG.ComponentClassification.RankTwoExceptional.F4Sec8

section Cert


theorem card_cen_tE_cert :
    Nat.card (Subgroup.centralizer ({tE} : Set F42C)) = 2 ^ 24 * 3 ^ 4 * 5 * 7 :=
  Certificates.certificate799601.1

theorem long_conj_tE (k : Fin 12) : IsConj tE (f4Rep (ZMod 2) [f4PairLong k]) :=
  Certificates.certificate799601.2.1 k

theorem conj_tE_or_uE (x : F42C) (hx : orderOf x = 2)
    (hc : Nat.card (Subgroup.centralizer ({x} : Set F42C)) = 2 ^ 24 * 3 ^ 4 * 5 * 7) :
    IsConj tE x ∨ IsConj uE x :=
  Certificates.certificate799601.2.2.1 x hx hc

theorem rho_not_conj : ¬IsConj rAE rBE ∧ ¬IsConj rAE zE ∧ ¬IsConj rBE zE :=
  Certificates.certificate799601.2.2.2

end Cert

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
