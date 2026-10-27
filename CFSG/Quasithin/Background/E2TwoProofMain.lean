module

public import CFSG.Quasithin.Background.E2TwoProofCase1
public import CFSG.Quasithin.Background.E2TwoProofCase2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native B6

namespace E2P

theorem e22StatementNoN_of_inputs (hF : E22Families)
    (h36 : A36CoreForSQTKCat) (h38 : A38ForSQTKCat) (hList : A23SQTKListFact)
    (hA21 : AsA21SQTKSection) : E2.E22StatementNoN := by
  intro Γ _ _ H T M hmp hsq hns
  obtain ⟨L, K, S⟩ := exists_setting hmp hsq hns
  refine ⟨⟨K, S.cComp, S.sup_eq, S.isQuasisimple_quotient_pCore h36, ?_⟩,
    sqtkGroup_star hA21 hmp hsq hns⟩
  by_cases hLn : L.Normal
  · exact S.cases_of_normal hF h36 hA21 hList hLn
  · exact S.cases_of_not_normal hF h38 hLn

end E2P

end CFSG.Quasithin
