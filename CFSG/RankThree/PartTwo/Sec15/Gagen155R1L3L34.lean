module

public import CFSG.RankThree.PartTwo.Sec13.Item131Facts
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProofNoL34

public section

namespace CFSG.RankThree.PartTwo.Sec15.GagenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem not_z3_l34_of_scriptY0
    (h131 : Item131) (h1513 : Item1513R) (h1510 : Item1510R)
    (hBr : Sec16.Step169TwoBridge) {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (hY0 : (scriptY0 A (lB A)).Nonempty) :
    ¬ Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) ×
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
  rintro ⟨φ⟩
  have hD : Sec13Data G A c L := hR.toSec13Data
  obtain ⟨hS, hZ⟩ := isPerfect_center_projSL 2 2 (by norm_num) (by norm_num)
  obtain ⟨-, h9, -, ⟨ψ⟩⟩ := facts_of_prod (S := CFSG.Assembly.RankThreeEven.projSL 3
    (GaloisField 2 2)) hD hS hZ φ
  exact Sec16.step163NoL34_of h131 h1513 h1510 hBr G A c L hR ⟨ψ⟩ h9 hY0

end CFSG.RankThree.PartTwo.Sec15.GagenL3
