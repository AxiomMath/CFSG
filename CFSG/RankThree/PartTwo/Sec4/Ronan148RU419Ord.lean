module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RU419Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

section Rows


theorem rowsU419Four : RowsU419Four := by
  intro X _ _ _ _ hX
  apply NoCfgU419.rowU419
  rcases Item419Res3.card_dvd_of_isList46Four hX with hd | hd | hd
  · exact noCfgU419_of_two_pow_nine hd (by decide)
  · exact noCfgU419_of_two_pow_nine hd (by decide)
  · exact noCfgU419_of_two_pow_nine hd (by decide)

theorem rowsU419Seven : RowsU419Seven := by
  intro X _ _ _ _ hX
  apply NoCfgU419.rowU419
  rcases Item419Res3.card_dvd_of_isList46Seven hX with hd | hd | hd
  · exact noCfgU419_of_two_pow_fifteen hd (by decide) (by decide)
  · exact noCfgU419_of_two_pow_fifteen hd (by decide) (by decide)
  · exact noCfgU419_of_two_pow_twentyone hd (by decide) (by decide) (by decide)

theorem rowsU419Eight : RowsU419Eight := by
  intro X _ _ _ _ hX
  apply NoCfgU419.rowU419
  obtain ⟨M, hd, h9⟩ := Item419Res3.not_two_pow_nine_dvd_of_isList46Eight hX
  exact noCfgU419_of_two_pow_nine hd h9

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R
