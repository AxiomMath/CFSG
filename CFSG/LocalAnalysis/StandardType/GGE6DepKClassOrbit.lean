module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKFormDefs

public section

namespace CFSG.StandardType

namespace E6Dep

private def orbTab : List (Vec6 × List (Fin 5)) :=
  [(![0, 0, 1, 2, 0, 0], [2, 3, 4]),
    (![0, 0, 2, 1, 0, 0], [2, 1, 0, 3, 2, 1]),
    (![0, 1, 1, 2, 0, 0], [2, 1, 3, 4]),
    (![0, 1, 2, 0, 0, 0], [2, 1, 3, 2, 4, 3]),
    (![0, 1, 2, 2, 0, 0], [2, 1, 3, 2, 4]),
    (![0, 2, 1, 0, 0, 0], [2, 1, 0]),
    (![0, 2, 1, 1, 0, 0], [2, 1, 0, 3]),
    (![0, 2, 2, 1, 0, 0], [2, 1, 0, 3, 2]),
    (![1, 1, 1, 2, 0, 0], [2, 1, 0, 3, 4]),
    (![1, 1, 2, 0, 0, 0], [2, 1, 0, 3, 2, 4, 3]),
    (![1, 1, 2, 2, 0, 0], [2, 1, 0, 3, 2, 4]),
    (![1, 2, 0, 0, 0, 0], [2, 1, 0, 3, 2, 1, 4, 3, 2]),
    (![1, 2, 2, 0, 0, 0], [2, 1, 0, 3, 2, 1, 4, 3]),
    (![1, 2, 2, 2, 0, 0], [2, 1, 0, 3, 2, 1, 4]),
    (![2, 1, 0, 0, 0, 0], []),
    (![2, 1, 1, 0, 0, 0], [2]),
    (![2, 1, 1, 1, 0, 0], [2, 3]),
    (![2, 2, 1, 0, 0, 0], [2, 1]),
    (![2, 2, 1, 1, 0, 0], [2, 1, 3]),
    (![2, 2, 2, 1, 0, 0], [2, 1, 3, 2])]

private theorem orbTab_acts : ∀ p ∈ orbTab, (evalWord gS p.2).mulVec p.1 = h0 := by
  decide +kernel

private theorem orbTab_complete :
    ∀ m : Vec6, m 4 = 0 → m 5 = 0 → m ≠ 0 → norm6 m = 0 → m ∈ orbTab.map Prod.fst := by
  decide +kernel

theorem iso_orbit {m : Vec6} (h4 : m 4 = 0) (h5 : m 5 = 0) (hm : m ≠ 0) (hq : norm6 m = 0) :
    ∃ sw : List (Fin 5), (evalWord gS sw).mulVec m = h0 := by
  obtain ⟨p, hp, hpm⟩ := List.mem_map.mp (orbTab_complete m h4 h5 hm hq)
  exact ⟨p.2, hpm ▸ orbTab_acts p hp⟩

end E6Dep

end CFSG.StandardType

end
