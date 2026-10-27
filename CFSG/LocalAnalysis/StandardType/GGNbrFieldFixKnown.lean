module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChev
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinear
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownSp
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownTwOmega
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixRows

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGFieldFixKnown.or {S T : ℕ → LargeEvenLabel → Prop} (hS : GGFieldFixKnown S)
    (hT : GGFieldFixKnown T) : GGFieldFixKnown fun p lab => S p lab ∨ T p lab :=
  fun p lab hp hp2 hlab h => h.elim (hS p lab hp hp2 hlab) (hT p lab hp hp2 hlab)

section Known

theorem ggFieldFixKnown_fieldFixLabel : GGFieldFixKnown GGFieldFixLabel :=
  fun p lab hp hp2 hlab h =>
    (ggFieldFixKnown_chev.or (ggFieldFixKnown_sp.or (ggFieldFixKnown_omegaPlus.or
      (ggFieldFixKnown_twOmega.or (ggFieldFixKnown_linear.or ggFieldFixKnown_E6)))))
      p lab hp hp2 hlab h.family

theorem ggNbrInnerWeylOn_fieldOtherOpen_of_fieldFix (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (h : GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldOtherOpenLabel p lab ∧
      ¬ GGFieldFixLabel p lab) :
    GGNbrInnerWeylOn GGNbrWeylFieldOtherOpenLabel :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG
    (ggFieldKLevel_of_fixKnown (fun _ _ h => h) ggFieldFixKnown_fieldFixLabel
      (fun _ _ hp hp2 hlab h => largeEvenLabelAll_rowPlain_of_fieldFixRowLabel hp hp2 hlab h)
      hpc hconj hcen hinn) h

end Known

end CFSG.StandardType

end
