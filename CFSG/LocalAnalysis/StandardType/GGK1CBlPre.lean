module

public import CFSG.LocalAnalysis.StandardType.GGK1CBlD1
public import CFSG.LocalAnalysis.StandardType.GGK1CBlD2
public import CFSG.LocalAnalysis.StandardType.GGK1CBlOne
public import CFSG.LocalAnalysis.StandardType.GGK1CBlIdx
public import CFSG.LocalAnalysis.StandardType.GGK1CBlDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal SpPrimaryBlocks spSupported
  symplectic_cross_prime_primary_centralizer_blocks)
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

theorem ggK1CBl_preblocks_exists {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hnf : 1 ≤ nf) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(StatedSp r K)} {m : List ℕ} (hm : GGK1CMultOf p nf d r K x m)
    (hx : x ^ p = 1) : Nonempty (ggK1CBl_PreBlocks p nf d r K x m) := by
  by_cases hx1 : x = 1
  · exact ggK1CBl_preblocks_one hnf hp hp2 hdvd hK hm hx hx1
  · haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcardK : Fintype.card K = 2 ^ nf := by rw [Fintype.card_eq_nat_card, hK]
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := nf) hcardK
    have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · exfalso; apply hx1; subst h0
        exact Subtype.ext (Subsingleton.elim (x : GL (Fin 0 ⊕ Fin 0) K) 1)
      · exact hpos
    haveI : NeZero r := ⟨by omega⟩
    have hproj : Function.Injective (proj r K) :=
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
        (r := r) (K := K)).1
    haveI : Fact p.Prime := ⟨hp⟩
    have ha : orderOf (proj r K x) = p :=
      orderOf_eq_prime (by rw [← map_pow, hx, map_one]) fun h => hx1 (hproj h)
    have hblocks : SpPrimaryBlocks 2 nf p x (proj r K x) :=
      (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hnf hK hp hp2
        hp2 hr (proj r K x) ha).2 x rfl (orderOf_eq_prime hx hx1)
    rcases hm.blocks_eq with ⟨hd1, P, hP, hmult⟩ | ⟨hd2, hmult⟩
    · subst hd1
      refine ⟨⟨ggK1CBl_Id1 K P m, ggK1CBl_A1 x P m, ggK1CBl_kind1 1 x P m, ?_, ?_, ?_, ?_, ?_⟩⟩
      · exact (ggK1CBl_comm_join_d1 hnf hp hK hx hm hP hblocks).1
      · exact (ggK1CBl_comm_join_d1 hnf hp hK hx hm hP hblocks).2.1
      · exact (ggK1CBl_comm_join_d1 hnf hp hK hx hm hP hblocks).2.2
      · exact ggK1CBl_kind_multiset_d1 hm hP hmult
      · exact ggK1CBl_witness_d1 hnf hp hK hm hP hblocks
    · subst hd2
      refine ⟨⟨ggK1CBl_Id2 K x m, ggK1CBl_A2 x m, ggK1CBl_kind2 x m, ?_, ?_, ?_, ?_, ?_⟩⟩
      · exact (ggK1CBl_comm_join_d2 hnf hp hdvd hK hx hm hblocks).1
      · exact (ggK1CBl_comm_join_d2 hnf hp hdvd hK hx hm hblocks).2.1
      · exact (ggK1CBl_comm_join_d2 hnf hp hdvd hK hx hm hblocks).2.2
      · exact ggK1CBl_kind_multiset_d2 hm hmult
      · exact ggK1CBl_witness_d2 hnf hp hdvd hK hx hm hblocks

end CFSG.StandardType

end
