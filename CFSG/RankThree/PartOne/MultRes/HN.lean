module

public import CFSG.RankThree.PartOne.Mult.Sporadic
public import CFSG.RankThree.PartOne.KS.HNFiveLocal

public section

namespace CFSG.RankThree.PartOne.MultRes

open CFSG.Blueprint CFSG.RankThree.PartOne.Mult

theorem sporadicKernelTrivial_hn_five :
    SporadicKernelTrivial .HN 5 := by
  intro E _ _ hE S _ π hS hπ hC hpg
  have h5 : ¬ 5 ∣ Nat.card π.ker :=
    HNRed.hnFiveKernelTrivial_of_interface KS.hnFiveLocalInterface_holds E hE S π hπ hS hC
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [hn, pow_zero])
  · exact absurd (hn ▸ dvd_pow_self 5 hpos.ne') h5

end CFSG.RankThree.PartOne.MultRes
