module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S217Two
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteenTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s21_15Torus_of_certificate113 (D : Data G)
    (Ch : Choice2011 G) : S21_15Torus D Ch :=
  s21_15Torus_of_szHone D Ch fun hX hT hTN hS hr hrn =>
    uc22ine229_exists_mem_normalizer_of_isSz hT hTN hS hX
      (CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hX) dvd_rfl hr hrn

theorem s21_15Two_of_certificate113 (D : Data G)
    (Ch : Choice2011 G) (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D) (h899 : F08.R899 D) :
    S21_15Two D Ch :=
  s21_15Two_of D Ch h211 hSg (s21_15Torus_of_certificate113 D Ch) h899

end CFSG.LocalAnalysis.UniquenessCase.UC22
