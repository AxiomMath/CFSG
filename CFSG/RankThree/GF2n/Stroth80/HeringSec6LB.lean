module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Index

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem stroth6LB_of_inputs (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hRoot : Stroth310RootStatement) : Stroth6LBStatement := by
  intro G _ _ M Q Z B hc n t hs
  have s5 := hs.toSec5
  refine ⟨fun m hm hsl => ?_, fun m hm hΩ => ?_⟩
  · obtain ⟨K, fK, finK, hK, hnat⟩ := HS6.slMNat_of_alt hsl
    obtain ⟨-, hcard⟩ := HS6.card_LB_of_relIndex h34 h311a hc hs
      (HS6.relIndex_SL h34 hc s5 hK hm hnat)
    rw [hcard]
    congr 2
    omega
  · rcases hΩ with hP | hM
    · by_cases hm3 : 3 ≤ m
      · obtain ⟨-, hcard⟩ := HS6.card_LB_of_relIndex h34 h311a hc hs
          (HS6.relIndex_omegaPlus h34 hRoot hc s5 hm3 hP)
        rw [hcard]
        congr 2
        omega
      · have hm2 : m = 2 := by omega
        subst hm2
        obtain ⟨-, hcard⟩ := HS6.card_LB_of_relIndex h34 h311a hc hs
          (HS6.relIndex_omegaPlus_four h34 hc hs hP)
        exact hcard
    · obtain ⟨-, hcard⟩ := HS6.card_LB_of_relIndex h34 h311a hc hs
        (HS6.relIndex_omegaMinus h34 hRoot hc s5 hm hM)
      rw [hcard]
      congr 2
      omega

end CFSG.RankThree.GF2n.Stroth80
