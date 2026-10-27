module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM1A

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9.MP

open scoped Matrix MatrixGroups
open CFSG.RankThree.GF2n.Stroth80.HS9.M1

@[expose] def SL2FactorStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
  ∀ (Mm : Type) [AddCommGroup Mm] [Module K Mm] [FiniteDimensional K Mm]
    (ρ : SL(2, K) →* (Mm ≃ₗ[K] Mm)) (X X' : Submodule K Mm), IsCompl X X' →
    (∀ a : K, (∀ m, ρ (uSL a) m - m ∈ X) ∧ ∀ x ∈ X, ρ (uSL a) x = x) →
    (∀ b : K, (∀ m, ρ (lSL b) m - m ∈ X') ∧ ∀ x ∈ X', ρ (lSL b) x = x) →
    (∀ m, (∀ g, ρ g m = m) → m = 0) →
    ∀ Θ : AddSubgroup (Mm →ₗ[K] (Fin 2 → K)),
      (∀ θ ∈ Θ, ∀ (a : K) m, θ (ρ (uSL a) m) = uMat a *ᵥ θ m) →
      (∀ x ∈ X, (∀ θ ∈ Θ, θ x = 0) → x = 0) →
      ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module K Y) (c : Mm ≃ₗ[K] (Fin 2 → Y)),
        ∀ g m, c (ρ g m) = smulVec (g : Matrix (Fin 2) (Fin 2) K) (c m)

end CFSG.RankThree.GF2n.Stroth80.HS9.MP
