module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Cat

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Sporadic.Schreier.Tits (titsD)

section Tits


theorem good427_titsD (y : titsD) (hy : orderOf y = 3) :
    Good427 (Subgroup.centralizer ({y} : Set titsD)) := by
  refine good427_of_not_five_dvd fun h5 => ?_
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({y} : Set titsD))
    5 h5
  have hzy : (z : titsD) * y = y * z := Subgroup.mem_centralizer_singleton_iff.mp z.2
  exact Item434RemTits.mul_ne_mul_of_orderOf hy (Or.inl rfl)
    (by rw [Subgroup.orderOf_coe, hz]) hzy.symm




theorem rowOf427_tits
    : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowOf427 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group := by
  intro ht
  refine rowOf427_of_noCfgS fun S _ _ _ hna ⟨e⟩ => ?_
  obtain ⟨e₀⟩ := CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.nonempty_mulEquiv_titsD_cat ht
  obtain ⟨hcard, hout⟩ := CFSG.LieType.SeitzGeneration.card_cat_tits_outer ht
  haveI : Finite (CFSG.LieType.SeitzGeneration.Cat ⟨.tits, ht⟩) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hout3 : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) :=
    not_three_dvd_outer_of_mulEquiv e (not_three_dvd_outer_of_le_two hout.le)
  refine ⟨noCfgS427_of_model (e.trans e₀) (center_eq_bot_of_simple_nonab hna) hout3 good427_titsD,
    noONS427_of_card ?_⟩
  rw [Nat.card_congr e.toEquiv]
  change ¬ 19 * 31 * 343 ∣ Nat.card (CFSG.LieType.SeitzGeneration.Cat ⟨.tits, ht⟩)
  rw [hcard]
  norm_num

end Tits

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
