module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Core
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Setup4Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

@[expose] def ofHuniq (standing : CFSG.LocalAnalysis.UniquenessCase.UC22.StandingGe3 G)
    (unique : uniqueFourUnique G) (M : Subgroup G) (maxLocal : uniqueFourIsMaxTwoLocal M)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (strong : IsStronglyPEmbedded p M)
    (huniq : ∀ D : Subgroup G, D ≠ ⊥ → IsPGroup 2 D →
      2 ≤ CFSG.Open.pRank p (normalizer (D : Set G) ⊓ M) → normalizer (D : Set G) ≤ M) :
    Sec7Core4 G where
  standing := standing
  M := M
  maxLocal := maxLocal
  p := p
  prime := hp
  odd := hp2
  strong := strong
  huniq := huniq
  rankK := fun _ hHM hrank _ hq => by
    exact R72.pRank_pPrimeCore_le_three_of_normalizer_le unique maxLocal hp strong huniq hHM
      hrank hq

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
