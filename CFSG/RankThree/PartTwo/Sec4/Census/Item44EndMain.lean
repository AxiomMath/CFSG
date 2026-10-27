module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndXExt
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndRep
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndLift
import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
import CFSG.FeitThompson.OddOrderTheorem

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG Subgroup

theorem oddCore_le_of_isSimpleGroup {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    {K : Subgroup G} [K.Normal] [IsSimpleGroup (G ⧸ K)] : oddCore G ≤ K :=
  le_of_isSolvable_of_normal inferInstance
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ABGDGroups.odd_card_oddCore G))

theorem partTwoRankThreeEndgame : PartTwoRankThreeEndgame := by
  intro G _ _ K _ hyp hnq
  obtain ⟨p, hp, hp5, ρ, hρ, hdet, a₀, ha₀2, ha₀⟩ := exists_rep hyp
  obtain ⟨-, hperf, hK, hsimple, -⟩ := hyp
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  set KX := K.map (QuotientGroup.mk' (oddCore G)) with hKX
  have : KX.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hOK : oddCore G ≤ K := oddCore_le_of_isSimpleGroup
  have : IsSimpleGroup ((G ⧸ oddCore G) ⧸ KX) :=
    (QuotientGroup.quotientQuotientEquivQuotient (oddCore G) K hOK).isSimpleGroup
  have hKXs : Group.IsSolvable KX :=
    Group.isSolvable_of_surjective ((QuotientGroup.mk' (oddCore G)).subgroupMap_surjective K)
  have hOX : oddCore (G ⧸ oddCore G) = ⊥ := CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot G
  have hz₀ : (a₀ : G ⧸ oddCore G) ∈ center (G ⧸ oddCore G) := by
    rw [mem_center_iff]
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      have h1 : ρ (g * a₀ * (a₀ * g)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, ha₀, mul_neg_one, neg_one_mul, mul_inv_cancel]
      have h2 := mk_eq_one_of_map_eq_one hρ h1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h2
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul] at h2
      exact h2
  have hneg : (-1 : GL (Fin 4) (ZMod p)) ≠ 1 := by
    intro h
    have h' : (-1 : Matrix (Fin 4) (Fin 4) (ZMod p)) = 1 := by
      have := congrArg (fun g : GL (Fin 4) (ZMod p) => (g : Matrix (Fin 4) (Fin 4) (ZMod p))) h
      simpa using this
    have h00 : (-1 : Matrix (Fin 4) (Fin 4) (ZMod p)) 0 0 =
        (1 : Matrix (Fin 4) (Fin 4) (ZMod p)) 0 0 := by rw [h']
    rw [Matrix.neg_apply, Matrix.one_apply_eq] at h00
    have h2 : (2 : ZMod p) = 0 := by
      calc (2 : ZMod p) = 1 - (-1) := by ring
        _ = 0 := by rw [h00, sub_self]
    exact CFSG.RankThree.PartTwo.two_ne_zero_zmod hp hp2 h2
  have hz₀1 : (a₀ : G ⧸ oddCore G) ≠ 1 := by
    intro h
    have ha₀O : a₀ ∈ oddCore G := (QuotientGroup.eq_one_iff a₀).mp h
    have ha₀1 : a₀ ≠ 1 := fun h' => hneg (by rw [← ha₀, h', map_one])
    have hord : orderOf a₀ = 2 := orderOf_eq_prime (by rw [sq, ha₀2]) ha₀1
    have := odd_orderOf_of_mem_oddCore' ha₀O
    rw [hord] at this
    exact (Nat.not_odd_iff_even.mpr even_two) this
  have hz₀2 : (a₀ : G ⧸ oddCore G) * a₀ = 1 := by
    rw [← QuotientGroup.mk_mul, ha₀2, QuotientGroup.mk_one]
  have H1 := le_center_of_normal_abelian hp2 hρ
  have H2 : ∀ t ∈ center (G ⧸ oddCore G), t * t = 1 → t = 1 ∨ t = (a₀ : G ⧸ oddCore G) := by
    intro t ht htt
    by_contra h
    push Not at h
    exact not_pCore_two_le_center (K := KX) hKXs hOX hnq
      (normal_two_le_center_of_involution hp5 hρ hdet ha₀ ht htt h.1 h.2 _ inferInstance
        pCore_isPGroup)
  exact endgame_of_facts (K := KX) hKXs hOX hnq hz₀ hz₀1 hz₀2 H1 H2
    (pairBound hp5 hρ hdet ha₀2 ha₀)

end CFSG.RankThree.PartTwo.Sec4.Census
