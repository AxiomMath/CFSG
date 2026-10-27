
module


public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QT2LocProof

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem centralizer_eta_one_le_Hj
    {x : J} (hx : x * eta uJ 11 1 = eta uJ 11 1 * x) : x ∈ Hj :=
  centralizer_le_Hj_of_T j4Facts one_mem_tMasks hx

theorem constrained_centralizer_eta_one :
    ∃ N : Subgroup J, N ≤ Subgroup.centralizer ({eta uJ 11 1} : Set J) ∧
      (∀ q ∈ Subgroup.centralizer ({eta uJ 11 1} : Set J), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧
      IsPGroup 2 ↥N ∧
      ∀ q ∈ Subgroup.centralizer ({eta uJ 11 1} : Set J), (∀ e ∈ N, q * e = e * q) → q ∈ N :=
  constrained_centralizer_T j4Facts one_mem_tMasks

end CFSG.Sporadic.J4.QT2
