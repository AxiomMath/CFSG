module

public import CFSG.LocalAnalysis.StandardType.GGL45NtAssembly
public import CFSG.LocalAnalysis.StandardType.GGL45NtVacHolds
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecHolds
public import CFSG.LocalAnalysis.StandardType.GGL45NtAutAsm
public import CFSG.LocalAnalysis.StandardType.GGL45NtSimp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45Nt_torusHKnownFormsOn_nonTorsion_of_core :
    (GGL45NtCoreOn GGL45NtFamCl) → (GGL45NtCoreOn GGL45NtFamEx) →
      GGL45TorusHKnownFormsOn GGL45FamNonTorsion :=
  fun hcoreCl hcoreEx =>
    ggL45TorusHKnownFormsOn_nonTorsion_of_nt (ggL45NtSimpOn_all _) ggL45NtVacOn_holds
      ggL45NtRecOn_cl hcoreCl ggL45NtAutOn_clAut ggL45NtRecOn_ex hcoreEx ggL45NtAutOn_ex

end CFSG.StandardType
