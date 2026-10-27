module

public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S11d.LieCentralizerSuzuki

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem lieGoodComponentFixT_POmegaOdd : LieGoodComponentFixT .POmegaOdd := by
  intro T _ _ p hp hp5 _ _ n f₀ hf₀ hmodel
  exfalso
  obtain ⟨⟨-, -, -, h2⟩, -⟩ := statedClassicalModel_of_lieModel_classical (by decide) hmodel
  exact absurd rfl h2

theorem lieGoodComponentFixT_twistedG2 : LieGoodComponentFixT .twistedG2 := by
  intro T _ _ p hp hp5 _ _ n f₀ hf₀ hmodel
  exfalso
  rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hR⟩ | ⟨-, h, -⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain ⟨⟨-, -, -, h3, -⟩, -⟩ := hR
    omega
  · exact absurd h (by decide)

theorem lieGoodComponentFixT_Tits : LieGoodComponentFixT .Tits := by
  intro T _ _ p hp hp5 _ _ n f₀ hf₀ hmodel
  exfalso
  rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hR⟩ | ⟨-, h, -⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain ⟨⟨-, -, -, -, h1⟩, -⟩ := hR
    have : 5 ≤ p * f₀ := by nlinarith
    omega
  · exact absurd h (by decide)

theorem lieGoodComponentFixT_twistedB2 :
    LieGoodComponentFixT .twistedB2 := by
  intro T _ _ p hp hp5 _ _ n f₀ hf₀ hmodel _ _ _ _ _ x hxp hx1 _ y hy2 hy1 hxy
  exact (false_of_twistedB2 hp hp5 hmodel hxp hx1 hy2 hy1 hxy).elim

end CFSG.RankThree.PartOne
