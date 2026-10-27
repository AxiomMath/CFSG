module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Context
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.UniqueFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

structure Sec7Core4 (G : Type) [Group G] [Finite G] where
  standing : CFSG.LocalAnalysis.UniquenessCase.UC22.StandingGe3 G
  M : Subgroup G
  maxLocal : CFSG.Open.uniqueFourIsMaxTwoLocal M
  p : ℕ
  prime : p.Prime
  odd : p ≠ 2
  strong : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M
  huniq : ∀ D : Subgroup G, D ≠ ⊥ → IsPGroup 2 D →
    2 ≤ CFSG.Open.pRank p (Subgroup.normalizer (D : Set G) ⊓ M) →
    Subgroup.normalizer (D : Set G) ≤ M
  rankK : ∀ H : Subgroup G, ¬ H ≤ M → 2 ≤ CFSG.Open.pRank p (H ⊓ M) →
    ∀ q : ℕ, q.Prime → CFSG.Open.pRank q ((CFSG.pPrimeCore p ↥H).map H.subtype) ≤ 3

namespace Sec7Core4

@[expose] def ofUnique (standing : CFSG.Yardstones.Mf4cdcdf2e013.Standing4 G)
    (unique : CFSG.Open.uniqueFourUnique G) (M : Subgroup G)
    (maxLocal : CFSG.Open.uniqueFourIsMaxTwoLocal M) (p : ℕ)
    (hp : p ∈ CFSG.Open.uniqueFourSigma M) (strong : IsStronglyPEmbedded p M) :
    Sec7Core4 G where
  standing := ⟨standing.simple, standing.nonab, standing.kProper, standing.charTwo,
    le_trans (by norm_num) standing.rank⟩
  M := M
  maxLocal := maxLocal
  p := p
  prime := hp.1.1
  odd := hp.1.2.1
  strong := strong
  huniq := normalizer_le_of_uniqueFourUnique unique maxLocal hp
  rankK := fun _ hHM hrank _ hq =>
    pRank_pPrimeCore_le_three_of_uniqueFourUnique unique maxLocal hp strong hHM hrank hq

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Counterexample4

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G]

@[expose] def toSec7Core4 (c : Counterexample4 G) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M) : Sec7Core4 G :=
  Sec7Core4.ofUnique c.standing c.unique c.S.M c.S.maxLocal p hp
    (c.isStronglyPEmbedded_of_mem_sigma hp)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Counterexample4

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4

variable {G : Type} [Group G] [Finite G]

theorem M_ne_top (k : Sec7Core4 G) : k.M ≠ ⊤ := by
  haveI := k.standing.simple
  exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top (H := k.M) k.standing.nonab
    k.maxLocal.1

theorem pPrimeCore_le_of_not_le (k : Sec7Core4 G) {H : Subgroup G}
    (hHM : ¬ H ≤ k.M) (hrank : 2 ≤ CFSG.Open.pRank k.p (H ⊓ k.M)) :
    (CFSG.pPrimeCore k.p ↥H).map H.subtype ≤ k.M :=
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.pPrimeCore_le k.strong k.prime hrank

theorem odd_card_pPrimeCore_of_not_le (k : Sec7Core4 G) {H : Subgroup G}
    (hHM : ¬ H ≤ k.M) (hrank : 2 ≤ CFSG.Open.pRank k.p (H ⊓ k.M)) :
    Odd (Nat.card (CFSG.pPrimeCore k.p ↥H)) :=
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.odd_card_pPrimeCore k.strong k.prime
    k.huniq hHM hrank

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4
