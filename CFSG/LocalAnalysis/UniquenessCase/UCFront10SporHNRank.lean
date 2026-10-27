module

public import Certificates.Certificate10509
public import CFSG.Sporadic.HNSchreier.Order
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.HNRank

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore

theorem hnT0_facts :
    HNT0Facts :=
  Certificates.certificate10509

theorem card_hnT0 :
    Nat.card hnT0 = 2 ^ 14 :=
  hnT0_facts.card

theorem isSylowTwoOf_hnT0 :
    IsSylowTwoOf hnT0 ⊤ := by
  have hidx : hnT0.index = 16664484375 := by
    have h1 := hnT0.card_mul_index
    rw [card_hnT0, card_JH] at h1
    norm_num at h1
    omega
  refine ⟨le_top, IsPGroup.of_card card_hnT0, ?_⟩
  rw [show (hnT0.subgroupOf ⊤).index = hnT0.index from Subgroup.relIndex_top_right _, hidx]
  decide

theorem t4J_mem_omegaOneCenterOf_thompsonJ :
    t4J ∈ omegaOneCenterOf (thompsonJ hnT0) :=
  hnT0_facts.t4_mem

theorem card_omegaOneCenterOf_thompsonJ_le :
    Nat.card (omegaOneCenterOf (thompsonJ hnT0)) ≤ 4 :=
  hnT0_facts.card_omega_le

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.HNRank

end
