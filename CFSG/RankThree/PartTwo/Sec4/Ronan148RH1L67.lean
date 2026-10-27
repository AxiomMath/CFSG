module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Wreath
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A8
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFWreath
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFLin

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG.RankThree.PartTwo.Sec4.Ronan148L (E27Move)
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt baseA)
open scoped MatrixGroups

section W6

open CFSG.RankThree.PartTwo.Sec4.RonanK429F.W6 (T tw s1 s2 s3 wreathFacts card_wreathW factorization_card_SL6)

@[expose] def movers6 : List SL(6, ZMod 2) := [s1, s2, s3, tw]

theorem moverCheck6 : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ∃ n ∈ movers6,
    n * vecElt T v ≠ vecElt T v * n ∧ n * vecElt T v ≠ vecElt T v ^ 2 * n := by
  decide +kernel

theorem sConj6 : ∀ j : Fin 3, (∃ w, s1 * T j = vecElt T w * s1) ∧
    (∃ w, s2 * T j = vecElt T w * s2) ∧ (∃ w, s3 * T j = vecElt T w * s3) := by
  decide +kernel

theorem movers6_mem {n : SL(6, ZMod 2)} (hn : n ∈ movers6) :
    n ∈ Subgroup.normalizer (baseA T : Set SL(6, ZMod 2)) := by
  have hs : ∀ m : SL(6, ZMod 2), (∀ j, ∃ w, m * T j = vecElt T w * m) →
      m ∈ Subgroup.normalizer (baseA T : Set SL(6, ZMod 2)) := by
    intro m hm
    refine mem_normalizer_baseA fun i => ?_
    obtain ⟨w, hw⟩ := hm i
    rw [hw, mul_inv_cancel_right]
    exact Item434Kit.vecElt_mem_baseA wreathFacts w
  simp only [movers6, List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact hs _ fun j => (sConj6 j).1
  · exact hs _ fun j => (sConj6 j).2.1
  · exact hs _ fun j => (sConj6 j).2.2
  · exact Item434Kit.t_mem_normalizer wreathFacts

theorem e27Move_sl6 : E27Move SL(6, ZMod 2) := by
  refine e27Move_of_wreath wreathFacts card_wreathW factorization_card_SL6 fun v hv => ?_
  obtain ⟨n, hn, h1, h2⟩ := moverCheck6 v hv
  refine ⟨n, movers6_mem hn, not_mem_normalizer_of_conj ?_⟩
  have hx3 : vecElt T v ^ 3 = 1 :=
    (Item434Kit.isElemAbelian_baseA wreathFacts).2 _ (Item434Kit.vecElt_mem_baseA wreathFacts v)
  have hx1 : vecElt T v ≠ 1 := fun h => hv (Item434Kit.vecElt_injective wreathFacts
    (h.trans vecElt_zero.symm))
  refine not_mem_zpowers_of_ne hx3 ?_ ?_ ?_
  · intro h
    apply hx1
    have h' : n * vecElt T v = 1 * n := by rw [← h]; group
    simpa using h'
  · intro h
    apply h1
    calc n * vecElt T v = (n * vecElt T v * n⁻¹) * n := by group
      _ = vecElt T v * n := by rw [h]
  · intro h
    apply h2
    have hinv : (vecElt T v)⁻¹ = vecElt T v ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact hx3
    calc n * vecElt T v = (n * vecElt T v * n⁻¹) * n := by group
      _ = (vecElt T v)⁻¹ * n := by rw [h]
      _ = vecElt T v ^ 2 * n := by rw [hinv]

theorem cubeInner_sl6 : CubeInner SL(6, ZMod 2) := by
  haveI : Finite (projSL 6 (GaloisField 2 1)) :=
    Finite.of_equiv _ (RonanK429F.projSLEquivSLZMod (n := 6) (by norm_num)).symm.toEquiv
  exact cubeInner_of_mulEquiv (RonanK429F.projSLEquivSLZMod (n := 6) (by norm_num)).symm
    (cubeInner_of_not_three_dvd_card_outer
      (Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (by norm_num)))

theorem rankThree_sl6 : RankThreeData SL(6, ZMod 2) :=
  rankThreeData_of_wreath wreathFacts cubeInner_sl6 (t := s3) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem l62_orderChecks :
    (∀ q, 2 ≤ q → q ^ 3 ∣ 20158709760 →
      20158709760 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∧
    (∀ q, 2 ≤ q → q ^ 3 ∣ 20158709760 →
      20158709760 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :=
  orderChecks_of_bound (B := 25) (by norm_num) (by decide +kernel)

end W6

section W7

open CFSG.RankThree.PartTwo.Sec4.RonanK429F.W7 (T tw s1 s2 s3 wreathFacts card_wreathW factorization_card_SL7)

@[expose] def movers7 : List SL(7, ZMod 2) := [s1, s2, s3, tw]

theorem moverCheck7 : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ∃ n ∈ movers7,
    n * vecElt T v ≠ vecElt T v * n ∧ n * vecElt T v ≠ vecElt T v ^ 2 * n := by
  decide +kernel

theorem sConj7 : ∀ j : Fin 3, (∃ w, s1 * T j = vecElt T w * s1) ∧
    (∃ w, s2 * T j = vecElt T w * s2) ∧ (∃ w, s3 * T j = vecElt T w * s3) := by
  decide +kernel

theorem movers7_mem {n : SL(7, ZMod 2)} (hn : n ∈ movers7) :
    n ∈ Subgroup.normalizer (baseA T : Set SL(7, ZMod 2)) := by
  have hs : ∀ m : SL(7, ZMod 2), (∀ j, ∃ w, m * T j = vecElt T w * m) →
      m ∈ Subgroup.normalizer (baseA T : Set SL(7, ZMod 2)) := by
    intro m hm
    refine mem_normalizer_baseA fun i => ?_
    obtain ⟨w, hw⟩ := hm i
    rw [hw, mul_inv_cancel_right]
    exact Item434Kit.vecElt_mem_baseA wreathFacts w
  simp only [movers7, List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact hs _ fun j => (sConj7 j).1
  · exact hs _ fun j => (sConj7 j).2.1
  · exact hs _ fun j => (sConj7 j).2.2
  · exact Item434Kit.t_mem_normalizer wreathFacts

theorem e27Move_sl7 : E27Move SL(7, ZMod 2) := by
  refine e27Move_of_wreath wreathFacts card_wreathW factorization_card_SL7 fun v hv => ?_
  obtain ⟨n, hn, h1, h2⟩ := moverCheck7 v hv
  refine ⟨n, movers7_mem hn, not_mem_normalizer_of_conj ?_⟩
  have hx3 : vecElt T v ^ 3 = 1 :=
    (Item434Kit.isElemAbelian_baseA wreathFacts).2 _ (Item434Kit.vecElt_mem_baseA wreathFacts v)
  have hx1 : vecElt T v ≠ 1 := fun h => hv (Item434Kit.vecElt_injective wreathFacts
    (h.trans vecElt_zero.symm))
  refine not_mem_zpowers_of_ne hx3 ?_ ?_ ?_
  · intro h
    apply hx1
    have h' : n * vecElt T v = 1 * n := by rw [← h]; group
    simpa using h'
  · intro h
    apply h1
    calc n * vecElt T v = (n * vecElt T v * n⁻¹) * n := by group
      _ = vecElt T v * n := by rw [h]
  · intro h
    apply h2
    have hinv : (vecElt T v)⁻¹ = vecElt T v ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact hx3
    calc n * vecElt T v = (n * vecElt T v * n⁻¹) * n := by group
      _ = (vecElt T v)⁻¹ * n := by rw [h]
      _ = vecElt T v ^ 2 * n := by rw [hinv]

theorem cubeInner_sl7 : CubeInner SL(7, ZMod 2) := by
  haveI : Finite (projSL 7 (GaloisField 2 1)) :=
    Finite.of_equiv _ (RonanK429F.projSLEquivSLZMod (n := 7) (by norm_num)).symm.toEquiv
  exact cubeInner_of_mulEquiv (RonanK429F.projSLEquivSLZMod (n := 7) (by norm_num)).symm
    (cubeInner_of_not_three_dvd_card_outer
      (Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (by norm_num)))

theorem rankThree_sl7 : RankThreeData SL(7, ZMod 2) :=
  rankThreeData_of_wreath wreathFacts cubeInner_sl7 (t := s3) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem l72_orderChecks :
    (∀ q, 2 ≤ q → q ^ 3 ∣ 163849992929280 →
      163849992929280 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∧
    (∀ q, 2 ≤ q → q ^ 3 ∣ 163849992929280 →
      163849992929280 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :=
  orderChecks_of_bound (B := 75) (by norm_num) (by decide +kernel)

end W7

section Row


theorem rowOf427_of_e27Move_model
    {X Y : Type} [Group X] [Group Y] (eXY : X ≃* Y)
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* X) →
      Subgroup.center L = ⊥)
    (hR : RankThreeData Y) (hmove : E27Move Y) : RowOf427 X := by
  intro S _ _ _ _ ⟨eSX⟩
  refine row427_of_e27Move (eSX.trans eXY) ?_ hR hmove
  intro L _ _ hS hL hZ3 ⟨e'⟩
  exact hZS L hS hL hZ3 ⟨e'.trans eSX⟩

theorem rowOf427_l62
    : RowOf427 (projSL 6 (GaloisField 2 1)) := by
  have hcard : Nat.card (projSL 6 (GaloisField 2 1)) = 20158709760 := by
    rw [Nat.card_congr (RonanK429F.projSLEquivSLZMod (n := 6) (by norm_num)).toEquiv]
    exact RonanK429F.W6.card_SL6
  refine rowOf427_of_e27Move_model (RonanK429F.projSLEquivSLZMod (n := 6) (by norm_num)) ?_
    rankThree_sl6 e27Move_sl6
  intro L _ _ hSL hL hZ3 ⟨e'⟩
  exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans hcard)
    l62_orderChecks.1 l62_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem rowOf427_l72
    : RowOf427 (projSL 7 (GaloisField 2 1)) := by
  have hcard : Nat.card (projSL 7 (GaloisField 2 1)) = 163849992929280 := by
    rw [Nat.card_congr (RonanK429F.projSLEquivSLZMod (n := 7) (by norm_num)).toEquiv]
    exact RonanK429F.W7.card_SL7
  refine rowOf427_of_e27Move_model (RonanK429F.projSLEquivSLZMod (n := 7) (by norm_num)) ?_
    rankThree_sl7 e27Move_sl7
  intro L _ _ hSL hL hZ3 ⟨e'⟩
  exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans hcard)
    l72_orderChecks.1 l72_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
