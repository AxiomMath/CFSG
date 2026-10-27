module

public import CFSG.RankThree.PartTwo.Sec21.FF84S410Hyp
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmParabolic
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmE27

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

theorem hypOmPair_holds : HypOmPair := fun {_ _} hs ht hst h0 => Om_pair hs ht hst h0

theorem hypOmParabolic_holds : HypOmParabolic := fun {_} ht h0 => Om_parabolic ht h0

theorem hypOmNormalizerE27_holds : HypOmNormalizerE27 := fun E hE h27 => Om_normalizer_E27 E hE h27

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
