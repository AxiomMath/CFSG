module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxL2
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxK

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped Pointwise commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type u} [Group Γ] {p : ℕ} {H A D D₁ D₂ E L R : Subgroup Γ}

structure K1Data (H A D₁ E L R K₁ : Subgroup Γ) : Prop where
  admits : Admits (H ⊔ A) K₁
  L_lt : L < K₁
  le_R : K₁ ≤ R
  min : ∀ M : Subgroup Γ, Admits (H ⊔ A) M → L ≤ M → M ≤ K₁ → M = L ∨ M = K₁
  sup_D₁ : K₁ ⊔ D₁ = R
  faithful : ∀ e ∈ E, (∀ x ∈ K₁, ⁅e, x⁆ ∈ L) → e = 1

namespace Red

theorem exists_K1Data [Finite Γ] (c : Red p H A D D₁ D₂ E L R) :
    ∃ K₁ : Subgroup Γ, K1Data H A D₁ E L R K₁ := by
  obtain ⟨r, hr, hrL⟩ := c.exists_prime
  obtain ⟨K, hK, hmax⟩ := c.exists_maximal_K
  obtain ⟨K₁, hK₁adm, hKK₁, hK₁R, hmin, hK₁D⟩ := c.exists_K₁ hK hmax
  obtain ⟨hKab, -⟩ := c.K_elem hrL hK.admits hK.L_le hK.le_R hK.ne
  have hF2 : ∀ e ∈ E, e ≠ 1 → K ⊔ (H ⊓ Subgroup.centralizer {e}) ⊔ A ≠ H ⊔ A :=
    fun e he he1 => c.ne_of_cen hK.admits hKab hK.le_R hK₁adm hK₁R hK₁D he he1
  have hKL : K = L := c.eq_L_of_ne hK.admits hKab hK.L_le hK.le_R hF2
  subst hKL
  exact ⟨K₁, hK₁adm, hKK₁, hK₁R, hmin, hK₁D, fun e he hcen =>
    c.eq_one_of_cen hK.admits hKab hK.le_R hK₁adm hK₁R hK₁D he hcen⟩

end Red

end CFSG.SignalizerFunctorTheorem.McBride.Near
