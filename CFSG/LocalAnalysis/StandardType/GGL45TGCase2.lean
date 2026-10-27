module

public import CFSG.LocalAnalysis.StandardType.GGL45TGURecipe

public section

namespace CFSG.StandardType.GGL45TG

open CFSG CFSG.Assembly

theorem ggL45TorusHKnownFormsOn_famTypeACase2 :
    GGL45TorusHKnownFormsOn GGL45FamTypeACase2 :=
  ggL45TorusHKnownFormsOn_of_split _ (fun p lab => GGL45FamTypeACase2 p lab ∧ lab.tag = .A)
    (fun p lab => GGL45FamTypeACase2 p lab ∧ lab.tag = .twA)
    (fun _ _ h => h.1.1.elim (fun ht => Or.inl ⟨h, ht⟩) (fun ht => Or.inr ⟨h, ht⟩))
    GGL45TA.ggL45TorusHKnownFormsOn_famTypeACase2_linear
    ggL45TorusHKnownFormsOn_famTypeACase2_unitary

end CFSG.StandardType.GGL45TG
