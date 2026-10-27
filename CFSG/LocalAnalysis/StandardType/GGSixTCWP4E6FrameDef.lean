module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Frame
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6ChainDefs

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

structure E6Frame (α₁ β₁ α₂ β₂ α₃ β₃ : Fin Tag.E6.rank → ℤ) : Prop where
  root₃ : IsRoot .E6 α₃
  root₃' : IsRoot .E6 β₃
  ip₃ : iform α₃ β₃ = -1
  orth₁ : iform α₁ α₃ = 0 ∧ iform α₁ β₃ = 0 ∧ iform β₁ α₃ = 0 ∧ iform β₁ β₃ = 0
  orth₂ : iform α₂ α₃ = 0 ∧ iform α₂ β₃ = 0 ∧ iform β₂ α₃ = 0 ∧ iform β₂ β₃ = 0
  mem : ∀ γ, IsRoot .E6 γ →
    (γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ ↔ (iform γ α₃ = 0 ∧ iform γ β₃ = 0))
  tab : ∀ γ, IsRoot .E6 γ → γ ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ →
    (iform γ α₃, iform γ β₃) ∈ tab12
  rootT : ∀ γ, IsRoot .E6 γ → γ ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ →
    (iform γ α₃, iform γ β₃) ∈ tcRootTab → ∀ m ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂, iform γ m = 0
  wtT : ∀ γ, IsRoot .E6 γ → γ ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ →
    (iform γ α₃, iform γ β₃) ∈ wtTab →
      (∃ m ∈ tcA2Set α₁ β₁, iform γ m ≠ 0) ∧ (∃ m ∈ tcA2Set α₂ β₂, iform γ m ≠ 0)
  chain : ∀ u₀ ∈ wtRep, ∃ δ : Fin 5 → (Fin Tag.E6.rank → ℤ), (∀ k, IsRoot .E6 (δ k)) ∧
    (∀ j k, iform (δ j) (δ k) = a5gram j k) ∧
    δ 0 ∈ tcA2Set α₁ β₁ ∧ δ 1 ∈ tcA2Set α₁ β₁ ∧ δ 3 ∈ tcA2Set α₂ β₂ ∧ δ 4 ∈ tcA2Set α₂ β₂ ∧
    δ 2 ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ ∧
    ((iform (δ 2) α₃, iform (δ 2) β₃) = u₀ ∨
      (iform (δ 2) α₃, iform (δ 2) β₃) = (-u₀.1, -u₀.2)) ∧
    ∀ γ, IsRoot .E6 γ →
      ((γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ ∨
          (γ ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ ∧
            ((iform γ α₃, iform γ β₃) = u₀ ∨ (iform γ α₃, iform γ β₃) = (-u₀.1, -u₀.2)))) ↔
        ∃ c ∈ std30, γ = tcChainVec c δ)

end CFSG.StandardType.TableCRes

end
