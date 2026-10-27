module

public import CFSG.RankThree.PartTwo.Sec13.K135K3He
public import CFSG.RankThree.PartTwo.Sec13.K135K3ON
public import CFSG.RankThree.PartTwo.Sec13.K135K3J4
public import CFSG.RankThree.PartTwo.Sec13.F135LastKDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

theorem kFactK3_holds :
    KFactK3 := by
  intro S _ _ p hS
  rcases hS with ⟨rfl, h | h⟩ | ⟨rfl, ⟨e⟩⟩
  · obtain ⟨e⟩ := h
    exact k3_He e
  · obtain ⟨e⟩ := h
    exact k3_ON e
  · exact k3_J4 e

end CFSG.RankThree.PartTwo.Sec13.F135Last
