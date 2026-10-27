module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeDefs

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly

@[expose] def TorusLiftNineInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    3 ∣ 2 ^ n + 1 → 9 ∣ 2 ^ n + 1 →
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* TwE6Delta.RecipeR K n),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      Nat.card (Subgroup.center L') = 3 →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A → 3 ^ 5 ≤ Nat.card A →
        (∀ a ∈ A, Induces ψ a) →
        ∃ E : Subgroup L', IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E ∧ ∀ a ∈ A, ∀ e ∈ E, a e = e

@[expose] def TorusLiftSixInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    3 ∣ 2 ^ n + 1 →
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* TwE6Delta.RecipeR K n),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      Nat.card (Subgroup.center L') = 3 →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A → Nat.card A = 3 ^ 6 →
        (∀ a ∈ A, Induces ψ a) →
        ∃ E : Subgroup L', IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E ∧ ∀ a ∈ A, ∀ e ∈ E, a e = e

theorem torusLiftSixInput_of_full (h : TorusLiftInput) : TorusLiftSixInput :=
  fun K _ _ n hn hK h3 L' _ _ ψ hψ hker hperf hZ A hA hcard hind =>
    h K n hn hK h3 L' ψ hψ hker hperf hZ A hA (by rw [hcard]; norm_num) hind

end CFSG.StandardType.TwE6D3
