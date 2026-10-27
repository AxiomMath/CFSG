module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.lemma_13_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Lemma 13 7 from BG Section 13 -/

section Section13

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- Lemma 13.7: if `E₁ ≠ 1` and `E₁` does not act regularly on `E₃`,
then `E₁E₃` acts in a prime manner on `M_σ`. -/
public theorem CFSG.lemma_13_7
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₁ne : E₁ ≠ ⊥)
    (hnotRegular : ¬ section13ActsRegularlyOn E₁ E₃) :
    section13ActsPrimeManner (E₁ ⊔ E₃) (section10Msigma M) := by
  classical
  rcases section13_nonregular_exists_prime_order_centralizing
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE hnotRegular with
    ⟨p, r, P, R, hP, hR_E₃, hR_CEP⟩
  exact section13_lemma_13_7_core
    (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
    (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (p := p) (r := r)
    hM hE hE₁ne hP hR_E₃ hR_CEP

end Section13
