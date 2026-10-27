module

public import CFSG.Open.QuasithinDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def OuterInvolutionData {A : Type} [Group A] (T N : Subgroup A) : Prop :=
  ∃ j ∈ T, j ∉ N ∧ j ^ 2 = 1 ∧ Nat.card ↥(T ⊓ Subgroup.centralizer ({j} : Set A)) = 32 ∧
    (∀ w ∈ T, (∀ t ∈ T, t * w = w * t) → w ≠ 1 →
      (∃ y ∈ T ⊓ Subgroup.centralizer ({j} : Set A), y ^ 2 = w) ∧
      ∀ x ∈ T ⊓ Subgroup.centralizer ({j} : Set A), x ^ 2 = 1 →
        (∃ y ∈ T ⊓ Subgroup.centralizer ({j} : Set A), y ^ 2 = x) → x = 1 ∨ x = w) ∧
    (∀ P : Subgroup A, P ≤ Subgroup.centralizer ({j} : Set A) → IsPGroup 2 P →
      Nat.card P ≤ 32) ∧
    ∀ u ∈ T ⊓ N, u ^ 2 = 1 → u ≠ 1 →
      ¬ ∃ f : ↥(T ⊓ Subgroup.centralizer ({u} : Set A)) →*
        ↥(T ⊓ Subgroup.centralizer ({j} : Set A)), Function.Injective f

@[expose] def AutJ2OuterInvolution : Prop :=
  ∀ (Y : Type) [Group Y] (T N : Subgroup Y), Nonempty (Y ≃* MulAut quasithinJ2) →
    IsSylowTwoOf T ⊤ → ⁅N, N⁆ = N → Nat.card T = 2 * Nat.card ↥(T ⊓ N) →
      OuterInvolutionData T N

end CFSG.Quasithin
