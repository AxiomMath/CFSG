module

public import CFSG.Quasithin.Vol2.Ch3E213MG41S1

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

variable {k : Type} [Field k] [CharP k 2]

@[expose] def SplitAt (G₀ : Subgroup (antiSp k)) (ρ x : Fin 4 → k) : Prop :=
  (∀ y ∈ Refl.normC G₀, ∀ μ : k, μ ≠ 0 → y - μ • x ∈ k ∙ ρ → μ = 1) ∨
  ∃ Q : (Fin 4 → k) → k,
    (∀ a b, spBil a ρ = 0 → spBil b ρ = 0 → Q (a + b) = Q a + Q b + spBil a b) ∧
    (∀ (c : k) a, spBil a ρ = 0 → Q (c • a) = c ^ 2 * Q a) ∧
    ∀ u ∈ Refl.normC G₀, spBil u ρ = 0 → u ∉ k ∙ ρ → Q u = 1

@[expose] def SectionSplit (G₀ : Subgroup (antiSp k)) : Prop :=
  ∀ ρ x w : Fin 4 → k, ρ ≠ 0 → x ∈ Refl.normC G₀ → w ∈ Refl.normC G₀ →
    spBil x ρ = 0 → spBil w ρ = 0 → spBil w x ≠ 0 → SplitAt G₀ ρ x

end CFSG.Quasithin.Ch3E213M.G41.Big
