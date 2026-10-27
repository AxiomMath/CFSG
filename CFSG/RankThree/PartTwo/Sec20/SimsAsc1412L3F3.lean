module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Index
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3F3L3
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3F3U3

public section

namespace CFSG.RankThree.PartTwo.Sec20

theorem gen_normalizer_omega1412
    {G : Type} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥) {p : ℕ} [Fact p.Prime] (hL : IsL3eps1412 ↥L p)
    {b : G} (hbL : b ∉ L) (hb2 : orderOf b = 2) {y : G} (hyL : y ∈ L) (hy3 : orderOf y = 3) :
    L ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) ⊔
      ⁅L ⊓ Subgroup.centralizer {b}, L ⊓ Subgroup.centralizer {b}⁆ := by
  obtain ⟨hp3, ⟨hp, ⟨e⟩⟩ | ⟨hp, ⟨e⟩⟩⟩ := hL
  · exact gen_normalizer_omega1412_L3 hC hp3 hp e hbL hb2 hyL hy3
  · exact gen_normalizer_omega1412_U3 hC hp3 hp e hbL hb2 hyL hy3

end CFSG.RankThree.PartTwo.Sec20
