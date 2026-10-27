module

public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylPlusLiftSL2

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggTorusLift_orthPlus_nonsplit
    {K : Type} [Field K] [Finite K]
    [CharP K 2] {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hm : 4 ≤ m) :
    GGTorusLift p (m - 1) (OrthRest.RPlus K m) := by
  obtain ⟨M, σ, hM, hσ⟩ := GGPlusLiftSL2.exists_order_p_inverting_sl2 hp hp2 hpq
  have hP := OrthRestTail.torusConcl_of_frame (OrthRestTail.plusFrame K m) hp hp2 hM hσ
    (by omega) (P := ⊥) (SP := ∅) bot_le (Set.empty_disjoint _) OrthRestTail.isElemAbelian_bot'
    bot_le (e := 0) (by rw [Subgroup.card_bot, pow_zero])
  rw [TableBOrth.coe_qPlusForm, add_zero] at hP
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard⟩ := OrthRestTail.exists_R_of_torusConcl
    (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (by omega)) hP
  obtain ⟨hZ, hZp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ m)
  exact OrthRest.ggTorusLift_of_R hp hZ hZp hU hU2 hEU hE hcard

theorem largeEvenLabelAll_torusLift_D_nonsplit
    {lab : LargeEvenLabel} (htag : lab.tag = .D) (hl : 4 ≤ lab.rank) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (lab.rank - 1) R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpn ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with hl3
  · omega
  obtain ⟨K, _, _, hK, hq⟩ := hQ
  have := CFSG.StandardType.charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hq,
    ggTorusLift_orthPlus_nonsplit hp hp2 (by rw [hK]; exact hpn) hl⟩

theorem ggCRN_lift_D_nonsplit
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .D) (hd : 24 ≤ 2 * lab.rank) (h3 : 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 9 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag h3 hd ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with hl3
  · omega
  obtain ⟨K, _, _, hK, hq⟩ := hQ
  have := CFSG.StandardType.charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hq, ggTorusLift_mono Nat.prime_three
    (ggTorusLift_orthPlus_nonsplit Nat.prime_three (by norm_num) (by rw [hK]; exact h3)
      (by omega)) (by omega)⟩

end CFSG.StandardType

end
