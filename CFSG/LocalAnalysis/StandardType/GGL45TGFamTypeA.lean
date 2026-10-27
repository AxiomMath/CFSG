module

public import CFSG.LocalAnalysis.StandardType.GGL45TGCase2
public import CFSG.LocalAnalysis.StandardType.GGL45TGCase1Rec

public section

namespace CFSG.StandardType.GGL45TG

open CFSG CFSG.Assembly

theorem ggL45TorusHKnownFormsOn_famTypeA :
    GGL45TorusHKnownFormsOn GGL45FamTypeA :=
  ggL45TorusHKnownFormsOn_of_split _ GGL45FamTypeACase1 GGL45FamTypeACase2 ggL45FamTypeA_split
    (ggL45TorusHKnownFormsOn_of_nt (ggL45NtSimpOn_famTypeA.antitone fun _ _ h => h.1)
      ggL45NtRecOn_famTypeACase1 ggL45NtCoreOn_famTypeACase1
      (ggL45NtH4On_famTypeA.antitone fun _ _ h => h.1))
    ggL45TorusHKnownFormsOn_famTypeACase2

end CFSG.StandardType.GGL45TG
