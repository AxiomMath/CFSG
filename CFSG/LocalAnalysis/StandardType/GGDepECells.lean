module

public import CFSG.LocalAnalysis.StandardType.GGDepECheck

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


open Certificates.DepASmall

@[expose] def ggDepEData : GGDepANData := [
  ((0, 1, 1, 1), [⟨0, [5, 3, 4, 1, 3, 2], 0, [6, 4, 1, 3, 0, 2]⟩, ⟨0, [6], 0, []⟩]),
  ((0, 2, 1, 1), [⟨0, [6], 0, []⟩, ⟨0, [2, 6], 0, [6]⟩]),
  ((0, 5, 1, 1), [⟨0, [6], 0, []⟩, ⟨0, [5, 6, 4, 3, 2], 0, [6, 4, 3, 2]⟩, ⟨0, [5, 0, 6, 2, 3, 4,
      1, 3, 2], 0, [6, 4, 5, 3, 4, 1, 3, 0, 2]⟩]),
  ((1, 3, 1, 1), [⟨0, [1, 3, 6, 5, 4, 1, 3, 2], 0, [2, 3, 6, 3, 4, 1, 3, 2]⟩, ⟨0, [1, 6, 1, 3, 2],
      0, [6, 1, 3, 2]⟩, ⟨0, [6, 1, 3, 2], 0, [1, 3, 2]⟩, ⟨0, [3, 4, 1, 3, 0, 2], 0, [6, 5, 4, 3,
      2]⟩, ⟨0, [6, 3, 2], 0, [1, 3, 2]⟩]),
  ((5, 0, 1, 1), [⟨0, [5, 6], 0, [6]⟩, ⟨0, [4, 5, 6, 2], 0, [6, 5, 6]⟩, ⟨0, [5, 0, 6, 2, 3, 4, 1,
      3, 2], 0, [6, 4, 5, 3, 4, 1, 3, 0, 2]⟩]),
  ((5, 1, 1, 1), [⟨0, [5, 3, 4, 1, 3, 2], 0, [6, 4, 1, 3, 0, 2]⟩, ⟨0, [5, 6, 1, 3, 2], 0, [6, 1,
      3, 2]⟩]),
  ((5, 4, 1, 1), [⟨0, [5, 6, 5, 4, 3, 2], 0, [6, 5, 4, 3, 2]⟩, ⟨0, [6, 4, 3, 2], 0, [5, 4, 3,
      2]⟩])
]

theorem ggDepE_cells : GGDepECells :=
  ggDepECheck_sound ggDepEData (by decide +kernel)

end CFSG.StandardType
