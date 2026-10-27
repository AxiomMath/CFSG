module

public import CFSG.LocalAnalysis.StandardType.GGL45NtVacRank1
public import CFSG.LocalAnalysis.StandardType.GGL45NtVacSz
public import CFSG.LocalAnalysis.StandardType.GGL45NtVacF1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45NtVacOn_holds :
    GGL45NtVacOn GGL45NtFamVac :=
  ((ggL45NtVacOn_rankOne.union ggL45NtVacOn_twB2).union ggL45NtVacOn_trivialF).antitone
    fun p lab ⟨h, hv⟩ => by
      simp only [GGL45NtVacLabel] at hv
      tauto

end CFSG.StandardType
