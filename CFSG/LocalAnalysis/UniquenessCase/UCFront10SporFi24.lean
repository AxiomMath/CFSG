module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporAt
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24C
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24Odd
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24P
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24TJ
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105InThompson
public import CFSG.Sporadic.Fi24.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

theorem k105SporAt_Fi24Prime
    : K105SporAt .Fi24Prime := by
  refine k105SporAt_of_k105In (Γ := ↥CFSG.Sporadic.Fi24.J) Fi24K.isSylowTwoOf_fi24T ?_
    CFSG.Sporadic.Fi24.fi24EquivJ
  exact k105In_top_of_thompson Fi24K.isSylowTwoOf_fi24T Fi24K.fi24z_mem_omegaOneCenter
    (Fi24K.k105In_centralizer_fi24z_of Fi24P.fi24P_k105) Fi24K.k105In_normalizer_thompsonJ
    Fi24K.fi24_odd

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
