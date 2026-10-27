
module

public import CFSG.LocalAnalysis.StandardType.L34SylowOvergroupBase

public import CFSG.LocalAnalysis.StandardType.L34SylowTabs
public import CFSG.LocalAnalysis.StandardType.PermStabilizerAlternatingSix
public import CFSG.LocalAnalysis.StandardType.SylowOvergroupReduction
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Certificate465003
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourGroupSpec
public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.StandardType.L34Sylow

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem overgroupFacts :
    OvergroupFacts :=
  have C := Certificates.certificate465003
  ⟨by rw [closureTabs_gensS]; exact card_S, C.card_P, C.P_le_S, C.aSix, C.trichotomy⟩

end CFSG.StandardType.L34Sylow
