module

public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_inf_centralizer_of_le {H K V : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hHV : H ≤ Subgroup.normalizer (V : Set G)) :
    H ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro m hm
  have h1 := Subgroup.mem_normalizer_iff.mp (hHK hm)
  have h2 := Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_centralizer hHV hm)
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact Subgroup.mem_inf.trans (((h1 c).and (h2 c)).trans Subgroup.mem_inf.symm)

end CFSG.Quasithin
