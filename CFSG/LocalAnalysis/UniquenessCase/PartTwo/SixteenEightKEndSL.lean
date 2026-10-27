module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKEndBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

theorem s16k_centralizer_sl_natural {Q : Type} [CommGroup Q] {L' : Subgroup (MulAut Q)} {n : ℕ}
    (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (h : (FFModel.nat (StatedSL n K)).Realizes L' ⊤ ⊥) :
    Subgroup.centralizer (L' : Set (MulAut Q)) = ⊥ :=
  s16k_centralizer_of_addCommutant hK
    (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedSL hn) h


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
