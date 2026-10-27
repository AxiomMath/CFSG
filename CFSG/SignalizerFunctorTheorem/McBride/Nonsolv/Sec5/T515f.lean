module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515f.Decomp

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem theorem_5_15_f
    {p : ℕ} {A G : Subgroup Γ} (h : KSetting p A G) (hKA : kDown G A = ⊥)
    {B : Subgroup Γ} (hBA : B ≤ A) :
    kOf (G ⊓ Subgroup.centralizer (B : Set Γ)) =
        kOf (kOf G ⊓ Subgroup.centralizer (B : Set Γ)) ∧
      lcal (G ⊓ Subgroup.centralizer (B : Set Γ)) =
        {Y | ∃ J ∈ lcal G, Y = CFSG.inSubgroup CFSG.generalizedFitting (smear J B)} ∧
      ∀ J ∈ lcal G, ∀ J' ∈ lcal G,
        CFSG.inSubgroup CFSG.generalizedFitting (smear J B) =
            CFSG.inSubgroup CFSG.generalizedFitting (smear J' B) ↔
          ∃ b ∈ B, J' = J.map (MulAut.conj b).toMonoidHom :=
  ⟨T515f.kOf_inf_centralizer_eq h hKA hBA, T515f.lcal_inf_centralizer_eq h hKA hBA,
    fun _ hJ _ hJ' => T515f.fitting_smear_eq_iff h hKA hBA hJ hJ'⟩

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
