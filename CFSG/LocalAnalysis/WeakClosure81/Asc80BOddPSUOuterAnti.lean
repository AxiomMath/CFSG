module

public import CFSG.ClassicalGroups.Unitary.Form
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterAntiCenter
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterAntiGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.UOuter

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem eq_top_of_comm_anti_conj (hσ : IsUnitaryInvolution σ) (h2K : (2 : K) ≠ 0)
    {H : Subgroup (SUid σ 4)} {A A' : Matrix (Fin 4) (Fin 4) K} {l : K} (hl : σ l * l = -1)
    (hAu : (A.map σ)ᵀ * A = 1) (hA'u : (A'.map σ)ᵀ * A' = 1) (hA2 : A * A = (l * l) • 1)
    (hA'2 : A' * A' = (l * l) • 1) (hcomm : A * A' = A' * A) (hne : A' ≠ A) (hne' : A' ≠ -A)
    (hH : ∀ g : SUid σ 4,
      (A * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (g : GL (Fin 4) K) * A ∨
        A' * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (g : GL (Fin 4) K) * A') →
      g ∈ H) :
    H = ⊤ := by
  obtain ⟨f₁, f₂, g₁, g₂, F⟩ := exists_antiFrame hσ h2K hl hAu hA'u hA2 hA'2 hcomm hne hne'
  exact eq_top_of_antiFrame hσ hl hAu hA'u F hH (isCenter_of_antiFrame hσ hl hAu hA'u F hH)

end CFSG.LocalAnalysis.WeakClosure81.UOuter
