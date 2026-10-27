module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTools
public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.GH74.GLS.IVK.L2.Fixed

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement Pointwise

namespace Proof1413Res6

variable {G : Type} [Group G] [Finite G]

theorem ne_three_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi X p e) : p ≠ 3 := by
  rintro rfl
  have h0 : 3 ^ e % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega : e ≠ 0))
  rcases hiso with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega

end Proof1413Res6

end CFSG.RankThree.PartTwo.Sec14
