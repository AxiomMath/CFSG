module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
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
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevRecipe
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggFieldFixKnown_E7E8
    : GGFieldFixKnown fun _ lab => lab.tag = .E7 ∨ lab.tag = .E8 := by
  intro p lab hp _ hlab hS
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · exact recipeChevalley_and (fun K _ _ hK _ _ f hf hord =>
      chev_fixStd (τ := .E7) (Or.inr (Or.inl rfl)) hn hK hp.pos hf hord) hQ
  · exact recipeChevalley_and (fun K _ _ hK _ _ f hf hord =>
      chev_fixStd (τ := .E8) (Or.inr (Or.inr rfl)) hn hK hp.pos hf hord) hQ

end CFSG.StandardType
