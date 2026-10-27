module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs4

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def TICorConfigHolds (G₀ : Type) [Group G₀] : Prop :=
  ∀ A₀ : Subgroup G₀, Nat.card A₀ = 4 → IsElemAbelian 2 A₀ → IsTISub G₀ A₀ → CorConfig G₀ A₀

@[expose] def FinG1 : Prop :=
  ∀ (G₀ : Type) [Group G₀], LieModel G₀ .PSL 3 2 2 → TICorConfigHolds G₀

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

namespace Assumption131

theorem false_of_ticorConfigHolds (h : Assumption131 G Γ VA i)
    (hVfix : ∀ A ∈ Γ, VA A ≤ fixSub A) {G₀ : Type} [Group G₀] (hG₀ : TICorConfigHolds G₀)
    (χ : G₀ →* LGL 2 V) (hχ : Function.Injective χ) (hχG : ∀ g, χ g ∈ G)
    {A₀ : Subgroup G₀} (hA : A₀.map χ ∈ Γ) (hr : mRank (A₀.map χ) ≤ i)
    (hcard : Nat.card A₀ = 4) (hel : IsElemAbelian 2 A₀) : False :=
  h.false_of_ti_of_finite hVfix χ hχ hχG hA hr (hG₀ A₀ hcard hel)

end Assumption131

end CFSG.LocalAnalysis.WeakClosure81

end
