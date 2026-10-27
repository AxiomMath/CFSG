module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.CentralizerK
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515e.Basic

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem theorem_5_15_e
    {p : ℕ} {A G X : Subgroup Γ} (h : KSetting p A G)
    (hX : IsDAInvariant A G X) (hKA : kDown G A = ⊥) (hK : khat X = X) : X ≤ khat G := by
  have hsol : sol G = ⊥ := sol_eq_bot_of_kDown_eq_bot hKA
  intro x hx
  rw [T515e.mem_khat_iff_of_sol_eq_bot hsol]
  refine ⟨hX.1 hx, fun J hJ => ?_⟩
  have hJA : J ∈ lcalA G A := (lcalA_eq_lcal_of_kDown_eq_bot h hKA).symm ▸ hJ
  have hJM : J ∈ mcalA G A := ⟨(mcal_eq_lcal_of_sol_eq_bot hsol).symm ▸ hJ, hJA.2⟩
  exact theorem_5_15_b h hX hJM hK hx

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
