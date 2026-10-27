module

public import Certificates.Certificate7470

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.Schreier.Tits _root_.Certificates


theorem burnsideF4nC_card_N1 (v : Fin 2925) (h0 : (0 : Fin 1755) ∈ titsLine v) (hv : v ≠ 0) :
    (burnsideF4nC_N1 v).ncard = 16 :=
  (Certificates.certificate7470.1 v h0 hv).1

theorem burnsideF4nC_trans_N1 (v : Fin 2925) (h0 : (0 : Fin 1755) ∈ titsLine v) (hv : v ≠ 0)
    {g g' : Equiv.Perm (Fin 1755)} (hg : g ∈ burnsideF4nC_N1 v) (hg' : g' ∈ burnsideF4nC_N1 v) :
    ∃ u ∈ titsJ ⊓ titsK, u * g * u⁻¹ = g' :=
  (Certificates.certificate7470.1 v h0 hv).2 g hg g' hg'

theorem burnsideF4nC_card_N2 (y : Fin 1755) (hy : y ∈ titsLine 0) (hy0 : y ≠ 0) :
    (burnsideF4nC_N2 y).ncard = 64 :=
  Certificates.certificate7470.2 y hy hy0

end CFSG.ASVolI
