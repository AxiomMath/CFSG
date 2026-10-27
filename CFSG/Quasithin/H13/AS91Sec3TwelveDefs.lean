module

public import CFSG.Quasithin.H13.AS91Sec3Defs

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

@[expose] def Stmt3_12M24 : Prop :=
  ∀ (l k : Finset (Finset (Fin 24))) (N : Subgroup S24), IsTrio l → IsTrio k →
    (Delta l k 3 ∨ Delta l k 4) → N ≤ M24g → (∀ σ ∈ N, σ • l = l) →
    (∀ σ ∈ M24g, σ • l = l → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N) → IsPGroup 2 N → Nat.card N = 64 →
    4 < ((fun σ : S24 => σ • k) '' (N : Set S24)).ncard

end CFSG.Quasithin.H13.AS91.M24G
