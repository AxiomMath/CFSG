module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Case1a
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Case1b
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Case2

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem lemma_5_14
    {p : ℕ} {A G X J : Subgroup Γ} (h : KSetting p A G) (hX : IsDAInvariant A G X)
    (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A) :
    CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤ X ∨
      X ≤ Subgroup.centralizer (J : Set Γ) := by
  by_cases hbot : projX G A J X ⊓ smear J A = ⊥
  · exact Or.inr (le_centralizer_of_projX_inf_eq_bot h hX.1 hX.2.1 hX.2.2 hsol hJ hbot)
  · exact Or.inl (fitting_smear_le_of_projX_inf_ne_bot h hX.2.1 hsol hJ hbot)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
