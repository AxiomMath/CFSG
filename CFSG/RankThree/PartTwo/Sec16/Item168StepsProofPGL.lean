module

public import CFSG.RankThree.PartTwo.Sec17.RouteWire17
import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
import CFSG.RankThree.PartTwo.Sec15.Item1511ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item136Pair

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

namespace Proof168Steps

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem not_isZ3PGLThreePi_of_item1514 (h : Sec17Std G A c L Y₀)
    (h1514 : Item1514 A (lB A) c L) (hMeets : MeetsY4 A (lB A) L Y₀) :
    ¬ Sec8.IsZ3PGLThreePi ↥(lBarA c L A) := by
  intro hPGL
  have hD : Sec13Data G A c L := h.toSec15R.toSec14Std.toSec13Data
  obtain ⟨⟨p, e, hp, he, hiso⟩, hZ, -⟩ := facts_of_isZ3PGLThreePi hD hPGL
  have hcL : c ∉ L := not_mem_of_center_eq_bot hD hZ
  have := hp
  rcases h1514 Y₀ h.mem_y0Star hMeets with ⟨-, -, -, hprod, -⟩ | ⟨⟨φ⟩, -⟩ |
      ⟨-, -, -, -, hno, -⟩
  · exact Proof1514.false_of_prod_of_isZ3PGLThreePi hD hcL hprod hPGL
  · exact Proof1511.not_isoLThreePi_of_A7 φ hiso
  · exact hno Y₀ h.mem_y0Star h.le_y0

end Proof168Steps

theorem noPGL131S17_of_item1514 (h1514 : Item1514S17) (hMeets : Claim1715Meets) :
    NoPGL131S17 :=
  fun G _ _ A c L Y₀ hs => Proof168Steps.not_isZ3PGLThreePi_of_item1514 hs
    (h1514 G A c L Y₀ hs) (hMeets G A c L Y₀ hs)

end CFSG.RankThree.PartTwo.Sec17
