module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGQ2PrimeBasic
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosRankAux4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {f n : ℕ} {ψ : Su K 2 f n →* G}

theorem ggNSLocal_rank_ge (h : GGNSLocalHyp p B Bs K f n ψ) : p ^ (n - 2) ≤ Nat.card B := by
  rcases h.bmax with hn | hb
  · exact (Nat.pow_le_pow_right h.prime.pos (by omega : n - 2 ≤ 4)).trans h.rank
  obtain ⟨E, U, hEab, hEcard, hU1, hU2, hEU⟩ := ggNSPosPC_rank_witness_aux h
  have hle : n - 2 ≤ LargeEvenTwoLocalRank p G :=
    CFSG.GGQ2Prime.le_twoLocalPrimeRank h.prime.two_le U E hU1 hU2 hEU hEab hEcard
  rw [hb.2.1]
  exact Nat.pow_le_pow_right h.prime.pos hle

end CFSG.StandardType

end
