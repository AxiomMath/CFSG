module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3RemTags

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGSixA3ConjKnown (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (G₀ D J : Subgroup X),
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU t n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f →
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (G₀ : Set X)) →
    D ≤ Subgroup.normalizer (G₀ : Set X) → (∀ b ∈ D, GGPsiInnerDiag (ggU t n f).D ψ b) →
    IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) → GGSixLSevenA3Case J →
      ∃ g ∈ G₀, D.map (MulAut.conj g).toMonoidHom ≤ J

@[expose] def GGSixA3ConjKnownTags : Prop :=
  GGSixA3ConjKnown .E6 ∧ GGSixA3ConjKnown .F4 ∧ GGSixA3ConjKnown .twistedE6

end Inputs

end CFSG.StandardType
