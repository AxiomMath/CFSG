module

public import CFSG.Quasithin.Background.F918X3
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin Matrix

section Additive

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {W : Type*} [CommGroup W]
  {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)} {π : ↥Γ →* ↥H}

theorem mem_realized_of_additive (hπ : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π)
    (α : MulAut ↥H) (θ : MulAut ↥Γ) (hθ : ∀ γ : ↥Γ, α (π γ) = π (θ γ))
    (Φ : (ι → K) ≃+ (ι → K))
    (hΦ : ∀ (γ : ↥Γ) (w : ι → K), Φ (((γ : GL ι K) : Matrix ι ι K) *ᵥ w) =
      (((θ γ : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ Φ w) :
    α ∈ realized H := by
  let T : MulAut (Multiplicative (ι → K)) := AddEquiv.toMultiplicative Φ
  refine mem_realized_of_twist_topBot (FFModel.nat_isActionModel Γ) rfl rfl hπ α θ hθ T ?_
  intro (γ : ↥Γ) (x : Multiplicative (ι → K))
  show T (natAct Γ γ x) = natAct Γ (θ γ) (T x)
  exact congrArg Multiplicative.ofAdd (hΦ γ (Multiplicative.toAdd x))

end Additive

end CFSG.Quasithin.F918X
