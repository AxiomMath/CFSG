module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs
public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.GGFamTame
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import CFSG.LocalAnalysis.StandardType.GGFamFieldDispatch
public import CFSG.LocalAnalysis.StandardType.GGFamTypeAField
public import CFSG.LocalAnalysis.StandardType.GGFamInnerDispatch
public import CFSG.LocalAnalysis.StandardType.GGFamOuterDHigh
public import CFSG.LocalAnalysis.StandardType.GGFamOuterDFour
public import CFSG.LocalAnalysis.StandardType.GGFamOuterEField
public import CFSG.LocalAnalysis.StandardType.GGFamTrivial

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem langFamilyCompFieldSL_holds
    : LangFamilyCompFieldSL := by
  intro τ L _ _ _ p₀ p S hτ hp hp2 ι a hT hap K hK
  by_cases h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1
  · have hTame : ∀ i : KernelComponent (famCharHom a),
        CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
          Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
      fun i => langFamTame_of_prime hτ S hp hp2 hT hap h1 i
    obtain ⟨i, hKi, hq⟩ :=
      exists_eq_rationalComponentM_of_isComponentOf S hp hτ hp2 hT hap h1 hTame hK
    refine ⟨i, ?_, ?_⟩
    · rw [hKi]
      exact (Subgroup.commutator_le_self _).trans inf_le_left
    · rw [hKi]
      exact langFamRatCompFieldLenSL_of_lanes langFamRatFieldSL_typeA langFamRatFieldSL_inner
          langFamRatFieldSL_outerD_high langFamRatFieldSL_outerD_four langFamRatFieldSL_outerE τ L p₀ S hτ p hp hp2 ι a hT hap h1 i hq
  · push Not at h1
    exact langFamilyCompFieldSL_trivial hτ S a h1 K hK

end CFSG.StandardType.TableCRes
