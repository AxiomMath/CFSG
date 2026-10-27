module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmO
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmP
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

theorem factParabRadical_holds : FactParabRadical := by
  intro Q _ _ hQ S B hS hB
  rcases hQ with ⟨K, _, _, hK, ⟨e⟩⟩ | hL | hP | hG
  · exact C11AmS.parabRadical_sl3 hK e hS hB
  · rcases hL with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact C11AmS.parabRadical_l34 h hS hB
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
  · rcases hP with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact C11AmS.parabRadical_sp4 h hS hB
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
  · exact C11AmS.parabRadical_g2 hG hS hB

end CFSG.Quasithin.Vol2.Ch11.SecS
