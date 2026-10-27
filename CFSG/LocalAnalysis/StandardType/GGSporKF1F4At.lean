module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped commutatorElement

@[expose] def BMPCentralF1At (p : ℕ) {K : Type} [Group K] (x : K) : Prop :=
  x ∈ BMOpCent p x ∧ ⁅BMOpCent p x, BMOpCent p x⁆ = Subgroup.zpowers x ∧
    BMOpCent p x ⊓ Subgroup.centralizer ((BMOpCent p x : Subgroup K) : Set K) =
      Subgroup.zpowers x ∧
    Subgroup.centralizer {x} ⊓ Subgroup.centralizer ((BMOpCent p x : Subgroup K) : Set K) ≤
      BMOpCent p x

@[expose] def BMPCentralF4At (p : ℕ) {K : Type} [Group K] (x : K) : Prop :=
  ∀ N : Subgroup K, N ≤ Subgroup.centralizer {x} →
    (∀ g ∈ Subgroup.centralizer ({x} : Set K), ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
      Subgroup.zpowers x ≤ N → N ≤ BMOpCent p x → N = Subgroup.zpowers x ∨ N = BMOpCent p x

end CFSG.StandardType.SporadicShape
