module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Module

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

private local instance : DecidableEq (Equiv.Perm (Fin 3)) :=
  Fintype.decidableEqEquivFintype

variable {G : Type} [Group G] [Finite G]

section General

variable {M L H : Subgroup G}

theorem Lgen_le_iff (hH : ∀ m ∈ M, conjSubgroup m H = H) :
    Lgen M L ≤ H ↔ L ≤ H := by
  constructor
  · intro h
    exact (le_Lgen_self M L).trans h
  · intro h
    rw [Lgen]
    refine iSup_le fun m => iSup_le fun hm => ?_
    calc conjSubgroup m L ≤ conjSubgroup m H := Subgroup.map_mono h
      _ = H := hH m hm

end General

variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem Lgen_le_XbarPre_iff (hc : Ctx M Q Z B) :
    Lgen M (LB M Q B) ≤ XbarPre M Q Z B ↔ LB M Q B ≤ XbarPre M Q Z B :=
  Lgen_le_iff (fun m hm => XbarPre_normal hc hm)

end CFSG.RankThree.GF2n.Stroth80
