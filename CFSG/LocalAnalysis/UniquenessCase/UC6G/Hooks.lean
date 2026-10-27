module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

structure Hooks (Dat : Data G) : Prop where
  nonempty : Dat.sig.Nonempty
  three_le : ∀ p ∈ Dat.sig, 3 ≤ CFSG.Open.pRank p Dat.M
  sig1_sp : ∀ p ∈ Dat.sig1, IsStronglyPEmbedded p Dat.M
  four_mem : ∀ r : ℕ, r.Prime → r ≠ 2 → 4 ≤ CFSG.Open.pRank r Dat.M → r ∈ Dat.sig
  three_mem_sub : ∀ H : Subgroup G, 3 < CFSG.Open.twoLocalPrimeRank 3 ↥H → 3 ∈ Dat.sig
  three_mem_top : 3 < CFSG.Open.twoLocalPrimeRank 3 G → 3 ∈ Dat.sig

namespace Hooks

variable {Dat : Data G} (hk : Hooks Dat)

include hk in
theorem pRank_le_three {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrσ : r ∉ Dat.sig) :
    CFSG.Open.pRank r Dat.M ≤ 3 := by
  by_contra h
  exact hrσ (hk.four_mem r hr hr2 (by omega))

end Hooks

end CFSG.LocalAnalysis.UniquenessCase.UC6G
