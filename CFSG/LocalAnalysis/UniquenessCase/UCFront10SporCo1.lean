module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporAt
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1K
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1N
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1Odd
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105InThompson

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

theorem k105SporAt_Co1 :
    K105SporAt .Co1 := by
  refine k105SporAt_of_k105In (Γ := CFSG.Blueprint.NativeSporadic.Co1) Co1K.isSylowTwoOf_co1Sylow
    ?_ (MulEquiv.refl _)
  refine k105In_top_of_thompson Co1K.isSylowTwoOf_co1Sylow Co1K.epsA_mem_quasithinOmegaOneCenter
    Co1K.k105In_centralizer_epsA ?_ Co1K.co1_odd
  rw [Co1K.thompsonJ_co1Sylow]
  exact Co1K.k105In_normalizer_epsHom_range

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
