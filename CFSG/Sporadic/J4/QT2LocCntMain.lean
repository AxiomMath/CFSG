
module

public import CFSG.Sporadic.J4.QT2LocCntMainBase

public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QT2LocCntProof

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem exists_conj_eta_three_of_mem_zMasks
    {c : ℕ} (hc : c ∈ zMasks) :
    ∃ g ∈ Hj, g * eta uJ 11 3 * g⁻¹ = eta uJ 11 c :=
  exists_conj_eta_three j4Facts.mat hc

theorem card_centralizer_eta_1131 :
    Nat.card ↥(Subgroup.centralizer ({eta uJ 11 1131} : Set J)) = 21799895040 :=
  card_centralizer_z0 j4Facts

theorem card_centralizer_eta_of_mem_zMasks
    {c : ℕ} (hc : c ∈ zMasks) :
    Nat.card ↥(Subgroup.centralizer ({eta uJ 11 c} : Set J)) = 21799895040 :=
  card_centralizer_of_mem_Zl j4Facts (mem_Zl.2 ⟨c, hc, rfl⟩)

theorem card_centralizer_eta_three :
    Nat.card ↥(Subgroup.centralizer ({eta uJ 11 3} : Set J)) = 21799895040 :=
  card_centralizer_eta_of_mem_zMasks three_mem_zMasks

end CFSG.Sporadic.J4.QT2
