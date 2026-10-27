module

public import CFSG.RankThree.GF2n.SzExplicit

public section

namespace CFSG.RankThree.S4Free.Stell

open CFSG.RankThree.GF2n.SzExplicit Matrix

@[expose] def IsNatSzProduct {G Y : Type*} [Group G] [CommGroup Y] (n : ℕ)
    (ψ : G →* CFSG.Open.Sz n) (ρ : G →* MulAut Y) : Prop :=
  ∃ (k : ℕ) (θ : Y ≃* Multiplicative (Fin k → Fin 4 → F n)),
    ∀ g y, θ (ρ g y) = Multiplicative.ofAdd fun j =>
      (((ψ g : CFSG.Open.Sz n) : GL (Fin 4) (F n)) : Matrix (Fin 4) (Fin 4) (F n)) *ᵥ
        Multiplicative.toAdd (θ y) j

end CFSG.RankThree.S4Free.Stell
