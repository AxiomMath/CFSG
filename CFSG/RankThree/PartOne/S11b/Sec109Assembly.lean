module

public import CFSG.RankThree.PartOne.S11b.Sec109LnTwoOuter
public import CFSG.RankThree.PartOne.S11b.Sec109EvenRankFour
public import CFSG.RankThree.PartOne.S11b.Sec109SylowModel

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial

namespace Sec109

theorem sec65LnTwo : Sec65LnTwo :=
  sec65LnTwo_of_evenRank lnTwoEvenRankFour

theorem lnTwoSylowSeven : LnTwoSylowSeven :=
  lnTwoSylowSeven_of_model lnTwoSylowSevenModel

theorem setup (hS : SchreierFor InCatalog) : Setup :=
  setup_of_inspections hS sec65LnTwo lnTwoOuter lnTwoSylowSeven

theorem inSec10Nine_of_remaining_steps (hS : SchreierFor InCatalog) (h112 : InSec11Two)
    (hwit : WitnessExists) (hcomp : ComponentExists) (hmax : MaximalExists)
    (hfield : FieldCaseImpossible) (hmixed : MixedCaseImpossible)
    (hinner : InnerCaseImpossible) : InSec10Nine :=
  inSec10Nine_of_steps h112 (setup hS) hwit hcomp hmax hfield hmixed hinner

end Sec109

end CFSG.RankThree.PartOne
