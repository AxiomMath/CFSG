module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsSixInf
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2116R
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21c
public import CFSG.Open.QTFaithfulEmptyTauCeti
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsSixteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s21_16R_of_s21_6Inf {D : Data G} {Ch : Choice2011 G} (h6 : S21_6Inf D Ch)
    (h12 : S21_12 D Ch) (h13 : S21_13 D Ch) (h14 : S21_14 D Ch)
    (hCA : CFSG.Open.QTFaithfulEmptyTauCeti.CatalogAgree) : S21_16R D Ch :=
  s21_16R_of_s21_16 (s21_16_of_s21_6Inf h6 h12 h13 h14 hCA)

end CFSG.LocalAnalysis.UniquenessCase.UC22
