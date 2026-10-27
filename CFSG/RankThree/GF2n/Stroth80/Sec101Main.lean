module

public import CFSG.RankThree.GF2n.Stroth80.Sec101Fusion
public import CFSG.RankThree.GF2n.Stroth80.Sec101Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec10Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec101Sat

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth101_of (h34 : Stroth34Statement) (hB2 : Stroth101EndStatement) :
    Stroth101Statement := by
  intro G _ _ M Q Z B hc n H
  by_contra hne
  have hno : ∀ t : G, ¬ Good101 M Q Z B t := fun t ht => hne ⟨t, ht⟩
  haveI := hc.normal_Q_in_M
  obtain ⟨X, hX, hBX⟩ := hc.exists_maxClique
  have hsat := hX.isSaturated hc H hno
  obtain ⟨S, hS, hSX, t, ht, ht1, htS, htc, htO⟩ :=
    IsSaturated101.exists_central_O2 h34 H hX.1 hsat hBX
  exact hB2 G M Q Z B hc n H hno X hX hsat hBX S hS t ht ht1 htS htc htO
    (IsSaturated101.isMulCommutative_wcl h34 H hX hsat hBX S hSX ht ht1 htc htO)

end CFSG.RankThree.GF2n.Stroth80
