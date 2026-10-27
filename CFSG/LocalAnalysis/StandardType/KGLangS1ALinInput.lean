module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGInputs
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
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinCont
import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem kgLangAxisS1LinInput_holds :
    KGLangAxisS1LinInput := by
  intro p lab hp hp2 hlab hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hsix, hsplit, hpn, htag⟩ := hS
  dsimp only at htag
  subst htag
  obtain ⟨hn, -⟩ : 1 ≤ n ∧ (1 ≤ l ∧ (l = 1 → 2 ≤ n)) := hlab
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  exact NbrGraphLinear.recipeLinear_all (d := l + 1) (N := 2 ^ n) (Q₀ := Q)
    (Q := KGLangAxisS1LinCont p)
    (fun F _ _ hF => kgLangS1A_lin_cont hp hp2 (lab := ⟨.A, l, n⟩) ⟨hsix, hsplit, hpn, rfl⟩ hn F
      hF) hQ

end CFSG.StandardType
