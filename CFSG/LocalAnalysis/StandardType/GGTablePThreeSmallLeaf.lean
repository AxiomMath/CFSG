module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSmallDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSmallTransport
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSmallG2
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSmallG2Der
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSmallTwB2
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSmallTwF4
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSmallTwF4Der

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.StandardType.SCFourCover

section Certs

private theorem svRank_triD4 :
    SVRank (fun t => t = .triD4) :=
  fun _ hlab ht => largeEvenLabelAll_threeRankTwo_triD4 hlab ht

theorem leafSmallVac_holds :
    LeafSmallVac := by
  intro X _ _ hX A δ J
  refine svTransport_holds _ ?_ X hX A δ J
  intro lab hlab hF
  rcases hF with h | h | h | h | h | h
  exacts [svRankG2_holds lab hlab h, svRankG2der_holds lab hlab h, svRank_triD4 lab hlab h,
    svRankTwB2_holds lab hlab h, svRankTwF4_holds lab hlab h, svRankTwF4der_holds lab hlab h]

end Certs

end CFSG.StandardType.TablePThreeKG

end
