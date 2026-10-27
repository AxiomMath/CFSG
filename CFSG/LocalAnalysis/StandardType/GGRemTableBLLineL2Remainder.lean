module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Cover
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo

public section

namespace CFSG.StandardType

section Certificates


theorem ggLNoInvariantLineInputOn_remainder_of_unitDvd_linTwo
    (h63 : GGLNoInvariantLineInputOn GGUnitDvd63Label)
    (hN : GGLNoInvariantLineInputOn fun p lab =>
      Yardstones.M3f9567aba59d.GGRemainderTableBLResLine p lab ∧ ¬ GGUnitDvdLabel p lab ∧
        ¬ GGLinTwoLabel p lab) :
    GGLNoInvariantLineInputOn Yardstones.M3f9567aba59d.GGRemainderTableBLResLine := by
  refine ggLNoInvariantLineInputOn_remainder_of_unitDvd
    LineU.ggLNoInvariantLineInputOn_unitDvd_holds h63 ?_
  refine CorFourTwoVacMore.lNoInvariantLineInputOn_mono (fun p lab h => ?_)
    (hN.or ggLNoInvariantLineInputOn_linTwo_holds)
  by_cases hc : GGLinTwoLabel p lab
  · exact Or.inr hc
  · exact Or.inl ⟨h.1, h.2, hc⟩

end Certificates

end CFSG.StandardType

end
