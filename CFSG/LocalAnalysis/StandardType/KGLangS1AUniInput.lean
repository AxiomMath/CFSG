module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGInputs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniCont
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem kgLangAxisS1UniInput_holds :
    KGLangAxisS1UniInput := by
  intro p lab hp hp2 hlab hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hsix, hsplit, hpn, htag⟩ := hS
  dsimp only at htag
  subst htag
  obtain ⟨hn, -⟩ : 1 ≤ n ∧ (2 ≤ l ∧ (l = 2 → 2 ≤ n)) := hlab
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  exact recipeUnitary_and (d := l + 1) (q := 2 ^ n) (Q := Q) (P := KGLangAxisS1UniCont p)
    (fun F _ _ hF => kgLangS1A_uni_cont hp hp2 (lab := ⟨.twA, l, n⟩) ⟨hsix, hsplit, hpn, rfl⟩ hn F
      hF) hQ

end CFSG.StandardType
