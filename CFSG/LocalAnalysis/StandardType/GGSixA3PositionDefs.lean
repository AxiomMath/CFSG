module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3KnownForms
public import CFSG.LieType.Steinberg.Minuscule.Datum
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.SeitzReduction
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.CurtisTits

section Position

@[expose] def GGA3Hyp (t : StatedLieTag) (X : Type) [Group X] (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (G₀ D J : Subgroup X) : Prop :=
  ψ.range = G₀ ∧ ψ.ker ≤ Subgroup.center (ggU t n f).K ∧
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f ∧
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (G₀ : Set X)) ∧
    D ≤ Subgroup.normalizer (G₀ : Set X) ∧ (∀ b ∈ D, GGPsiInnerDiag (ggU t n f).D ψ b) ∧
    IsElemAbelian 3 D ∧ Nat.card D = 3 ^ 2 ∧
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) ∧ GGSixLSevenA3Case J

end Position

end CFSG.StandardType
