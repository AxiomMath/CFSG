module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksDefs

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.Open (IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def OrthTorusConj : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2] (t : ℕ) (δ : Fin 2), Nat.card K = 2 →
    4 ≤ t + δ.val → ∀ A : Subgroup ↥(omegaQ (K := K) t δ), IsElemAbelian 3 A →
    (∀ g : ↥(omegaQ (K := K) t δ), (∀ a ∈ A, g * a = a * g) → g ^ 3 = 1 → g ∈ A) →
    ∃ (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
      (P : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K),
      Function.Injective ζ ∧
      (∀ v, planeQ (K := K) t δ ((P : Matrix _ _ K) *ᵥ v) = planeQ (K := K) t δ v) ∧
      ∀ x : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K,
        (∃ a ∈ A, x = P * (a : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹) ↔
          ∃ u : PlaneRaw.V t, x = otau ζ t δ u

end

end CFSG.StandardType.GGQ2Frame.OrthBlocks
