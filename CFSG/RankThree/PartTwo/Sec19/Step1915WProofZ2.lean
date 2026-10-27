module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12ThreeCentralZ2
public import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie9
public import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1915WProof

theorem step1917Z2W_of
    (h1913 : Step1913) (hAut : KS1917Lie3AutCent) : Step1917Z2W :=
  Sec19.step1917Z2W_of h1913
    (step1917Z2KFact_of step1917Z2KM12 step1917Z2KLie9 (step1917Z2KLie3_of_aut hAut))

end CFSG.RankThree.PartTwo.Sec19.Step1915WProof
