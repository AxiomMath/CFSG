module

public import CFSG.RankThree.GF2n.Tim79a34G0Fit
public import CFSG.RankThree.GF2n.Tim79a34G0Bar

public section

namespace CFSG.RankThree.GF2n.Tim79a

theorem ntQEOutResidualStatement_holds : NTQEOutResidualStatement :=
  ntQEOutResidualStatement_of_fields fun _ _ _ _ _ _ _ _ hH hZ hn hrel hOut =>
    ⟨(residualFitNotWC hH hZ hn hrel hOut).1, (residualFitNotWC hH hZ hn hrel hOut).2,
      residualBarFields hH hZ hn⟩

end CFSG.RankThree.GF2n.Tim79a
