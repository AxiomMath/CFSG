module

public import CFSG.Quasithin.H13.GoldEdgeS3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GoldschmidtPair

public section

namespace CFSG.Quasithin.H13

theorem goldschmidtEdgeBoundS3_holds :
    GoldschmidtEdgeBoundS3 :=
  fun _ _ _ _ _ h => CFSG.AGLEmbeddingD2.card_inf_le_two_pow_seven_of_vPair h.toVPair

end CFSG.Quasithin.H13
