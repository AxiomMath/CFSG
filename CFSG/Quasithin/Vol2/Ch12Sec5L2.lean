module

public import CFSG.Quasithin.Vol2.Ch12Sec5Ir
public import CFSG.Quasithin.Vol2.Ch12Sec5F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125

theorem lemma12_5_2_of (h1222 : Stmt12_2_2) : Lemma12_5_2 := by
  intro G _ _ T L V F hH
  obtain ⟨g1, g2, g3⟩ := S125L2G.part1_groups h1222 F hH
  obtain ⟨i1, i2, i3⟩ := S125Ir.part1_irr h1222 F hH
  obtain ⟨a1, a2, a3, a4⟩ := S125L2G.part2_groups h1222 F hH
  obtain ⟨b1, b2, b3, b4⟩ := S125L2G.part3_groups h1222 F hH
  obtain ⟨c1, c2, c3, c4⟩ := S125L2G.part4_groups h1222 F hH
  exact ⟨⟨g1, g2, g3, i1, i2, i3⟩, ⟨a1, a2, a3, a4, S125Nat.part2_nat h1222 F hH⟩,
    ⟨b1, b2, b3, b4, S125Nat.part3_nat h1222 F hH⟩,
    ⟨c1, c2, c3, c4, S125Nat.part4_ext h1222 F hH, S125F.part4_f h1222 F hH⟩⟩

end CFSG.Quasithin.H13
