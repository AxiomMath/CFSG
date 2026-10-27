module

public import Certificates.Certificate8056
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Certificates CFSG.CosetTable

theorem tabA_inv :
    (∀ x, ofTab tabAi (ofTab tabA x) = x) ∧ ∀ x, ofTab tabA (ofTab tabAi x) = x :=
  Certificates.certificate8056.1

theorem tabB_inv :
    (∀ x, ofTab tabBi (ofTab tabB x) = x) ∧ ∀ x, ofTab tabB (ofTab tabBi x) = x :=
  Certificates.certificate8056.2.1

theorem tabQ_inv :
    (∀ x, ofTab tabQi (ofTab tabQ x) = x) ∧ ∀ x, ofTab tabQ (ofTab tabQi x) = x :=
  Certificates.certificate8056.2.2

@[expose] def permA :
    Equiv.Perm (Fin 162) := ⟨ofTab tabA, ofTab tabAi, tabA_inv.1, tabA_inv.2⟩

@[expose] def permB :
    Equiv.Perm (Fin 162) := ⟨ofTab tabB, ofTab tabBi, tabB_inv.1, tabB_inv.2⟩

@[expose] def permQ :
    Equiv.Perm (Fin 162) := ⟨ofTab tabQ, ofTab tabQi, tabQ_inv.1, tabQ_inv.2⟩

@[expose] def psi : Fin 3 → Equiv.Perm (Fin 162) :=
  ![permA, permB, permQ]

@[expose] def w3 (i : Fin 360) : List (Fin 3 × Bool) :=
  (w360.getD i.val []).map fun k => (k.castSucc, true)

abbrev relsAB : List (List (Fin (subsetOf 3 [0, 1]).length × Bool)) :=
  restrictWords (subsetOf 3 [0, 1]) relsQ

end CFSG.Timmesfeld.Moufang.Deep
