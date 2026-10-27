module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOMBlocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub
open scoped commutatorElement

theorem s16t3_orthMinus_card_binary {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) :
    Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadTail 0 (minusTailForm K 1 1))) = 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsF2 K :=
    IsF2.of_natCard_eq_two (by rw [Nat.card_eq_fintype_card]; exact hK)
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2) hK
  have hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0 := irreducible_one_one
  have hO := orthMinus_card_orthogonalGroup_tail_zero (K := K) (b := 1) (c := 1) hirr
  rw [hO, Nat.card_eq_fintype_card, hK]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
