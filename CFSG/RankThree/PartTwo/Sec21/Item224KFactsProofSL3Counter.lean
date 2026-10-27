module

public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof

open Matrix CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_sq
  slGraphAut_field_commute slGraphAut_matrix)

namespace SL3Counter

noncomputable section

abbrev F64 : Type := GaloisField 2 6

instance : Fintype F64 := Fintype.ofFinite F64

end

end SL3Counter

open SL3Counter

end CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof
