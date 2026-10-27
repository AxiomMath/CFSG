module

public import CFSG.Quasithin.Background.E2TwoProofDefs

public section

namespace CFSG.Quasithin.Ch3E213M.OL

open CFSG.Open

@[expose] def KFactL3U3OuterInv : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p →
    ((p % 4 = 1 ∧ IsPSU 3 p 1 K) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 K)) → ∀ S : Sylow 2 K,
    ∃ z : K, orderOf z = 2 ∧ E2P.zOf (S : Subgroup K) = Subgroup.zpowers z ∧
      (∀ Q : Subgroup K, Q ≤ Subgroup.centralizer ({z} : Set K) → IsPGroup 2 Q →
        Subgroup.centralizer ({z} : Set K) ≤ Subgroup.normalizer (Q : Set K) →
        Q ≤ Subgroup.zpowers z) ∧
      ∀ v : MulAut K, orderOf v = 2 →
        (∀ x ∈ Subgroup.centralizer ({z} : Set K), v x * x⁻¹ ∈ Subgroup.zpowers z) →
        v ∈ (MulAut.conj : K →* MulAut K).range

@[expose] def KFactL33NoQuadFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsPSL 3 3 1 ↥K →
    Subgroup.centralizer (K : Set X) = ⊥ → ∀ S : Sylow 2 ↥K,
    ∃ z : ↥K, orderOf z = 2 ∧ E2P.zOf (S : Subgroup ↥K) = Subgroup.zpowers z ∧
      ∀ V : Subgroup X, IsElemAbelian 2 V → 4 ≤ Nat.card V →
        V ≤ pCoreOf 2 (Subgroup.centralizer ({(z : X)} : Set X)) →
      ∀ (W : Type) [Group W] [Finite W], (∀ a b : W, a * b = b * a) → (∀ a : W, a * a = 1) →
      ∀ ρ : X →* MulAut W, (∃ k ∈ K, ρ k ≠ 1) →
        ∃ v ∈ V, ∃ v' ∈ V, ∃ w : W, ρ v (ρ v' w * w⁻¹) * (ρ v' w * w⁻¹)⁻¹ ≠ 1

end CFSG.Quasithin.Ch3E213M.OL
