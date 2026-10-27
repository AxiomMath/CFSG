module

public import Certificates.Certificate725009

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row.HS119

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier


theorem hs119_le_of_ruleClosed {R' : Subgroup (Equiv.Perm (Fin 3850))} (hPR : hsP ≤ R')
    (hRR : R' ≤ hsR) {A C : Subgroup (Equiv.Perm (Fin 3850))} (hAS : A ≤ hsS ⊓ R')
    (hA2 : ∀ a ∈ A, a * a = 1) (hA8 : 8 ≤ Nat.card A) (hSC : hsS ⊓ R' ≤ C)
    (hcl : ∀ g ∈ R', Nat.card A ≤ 4 * Nat.card ↥(A.map (MulAut.conj g).toMonoidHom ⊓ C) →
      A.map (MulAut.conj g).toMonoidHom ≤ C) :
    R' ≤ C :=
  Certificates.certificate725009 hPR hRR hAS hA2 hA8 hSC hcl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row.HS119
