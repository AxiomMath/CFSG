module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Root
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6A5Std

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def a5gram (j k : Fin 5) : ℤ :=
  if j = k then 2 else if (j : ℕ) + 1 = k ∨ (k : ℕ) + 1 = j then -1 else 0

@[expose] def tcChainVec (c : List ℤ) (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) :
    Fin Tag.E6.rank → ℤ :=
  ∑ k : Fin 5, c.getD k.val 0 • δ k

structure A5Chain (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) : Prop where
  root : ∀ k, IsRoot .E6 (δ k)
  gram : ∀ j k, iform (δ j) (δ k) = a5gram j k

@[expose] def tcChainSet (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) : Set (Fin Tag.E6.rank → ℤ) :=
  {γ | ∃ c ∈ std30, γ = tcChainVec c δ}

structure A5Swap (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) : Prop where
  s0 : ∃ c ∈ stdX2, ρ (δ 0) = tcChainVec c δ
  s1 : ∃ c ∈ stdX2, ρ (δ 1) = tcChainVec c δ
  s2 : ∃ c ∈ stdFneg, ρ (δ 2) = tcChainVec c δ
  s3 : ∃ c ∈ stdX1, ρ (δ 3) = tcChainVec c δ
  s4 : ∃ c ∈ stdX1, ρ (δ 4) = tcChainVec c δ

end CFSG.StandardType.TableCRes

end
