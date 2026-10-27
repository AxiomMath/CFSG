module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R1621 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, Hyp16 D V₀ V →
    ∃ p : ℕ, D.sig = {p} ∧
      ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({v} : Set G))

@[expose] def R1622 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, Hyp16 D V₀ V → ∀ g : G, g ∉ D.M → ∀ U : Subgroup G, U ≤ V →
    rankThreeGamma 1 2 U ≤ D.M → conjSubgroup U g ⊓ V = ⊥

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
