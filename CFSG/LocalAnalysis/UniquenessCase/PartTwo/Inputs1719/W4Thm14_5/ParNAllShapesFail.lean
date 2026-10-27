module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapes
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.RankOne
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.NaturalClassicalQuasisimple
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneABoundShape
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.XOrth
import all CFSG.Timmesfeld.Orders.Distinct
import CFSG.Adapters.LieModelOrders
import CFSG.Adapters.LieModelSimple
import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusPiecesOrders
public import CFSG.ClassicalGroups.Orthogonal.Models
public import CFSG.LieType.Universal.Symplectic
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Blueprint (LieModel)

theorem lieModel_quot_center_of_isSpn {X : Type} [Group X] {m k : ℕ} (h : IsSpn X (2 * m) k)
    (hm : 3 ≤ m) (hk : 1 ≤ k) : LieModel (X ⧸ Subgroup.center X) .PSp m 2 k := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  let : Field K := hKf
  let : Finite K := hKfin
  rw [show 2 * m / 2 = m by omega] at e
  have hZ : (Subgroup.center X).map e.toMonoidHom =
      (StatedScalars (Fin m ⊕ Fin m) K).subgroupOf (StatedSp m K) := by
    have h1 : (Subgroup.center X).map e.toMonoidHom = Subgroup.center ↥(StatedSp m K) :=
      Subgroup.map_center_eq e
    rw [h1, CFSG.LieType.Universal.Symplectic.center_eq m K]
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, hk, by omega, by simp; omega⟩,
    K, hKf, hKfin, hK, ⟨QuotientGroup.congr _ _ e hZ⟩⟩

theorem isU4_quot_center_of_isSUn_four {X : Type} [Group X] {a : ℕ} (h : IsSUn X 4 a)
    (ha : 1 ≤ a) : IsU4 (X ⧸ Subgroup.center X) a := by
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  let : Field K := hKf
  let : Finite K := hKfin
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ((4 : ℕ), 2 ^ a) ≠ (3, 2) := fun hpair =>
    absurd (congrArg Prod.fst hpair) (by norm_num)
  have hZ : (Subgroup.center X).map e.toMonoidHom =
      (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ a) K) := by
    have h1 : (Subgroup.center X).map e.toMonoidHom = Subgroup.center ↥(StatedSU 4 (2 ^ a) K) :=
      Subgroup.map_center_eq e
    rw [h1, (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := a)
      (F := K) (n := 4) hK (by norm_num) hne).2]
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, ha, by norm_num, by simp⟩,
    K, hKf, hKfin, hK, ⟨QuotientGroup.congr _ _ e hZ⟩⟩

theorem ordBC_two_ne_ordTwistedA {f u g : ℕ} (hf : 1 ≤ f) (hu : 2 ≤ u) (hg : 1 ≤ g) :
    ordBC 2 (2 ^ f) ≠ ordTwistedA u (2 ^ g) :=
  ne_ordTwistedA_of_dvd_closed (profile_ordBC hf) zBC_dvd_closed
    ((profile_ordBC hf).ne_small (by omega) (by omega)) hu hg

private theorem not_nParamSingle_of_lowOrder {X : Type} [Group X] {N : ℕ}
    (hlow : LowOrder (Nat.card X) N)
    (hZ : CFSG.Open.IsQuasisimple X → Odd (Nat.card (Subgroup.center X)))
    (hL3 : ∀ f, 1 ≤ f → Nat.card (X ⧸ Subgroup.center X) ≠ ordA 2 (2 ^ f))
    (hSp4 : ∀ f, 1 ≤ f → Nat.card X ≠ ordBC 2 (2 ^ f)) {n : ℕ} : ¬ NParamSingle X n := by
  rintro (hSz | hL2 | hSU3 | hSL3 | hSp4')
  · exact false_of_rankOne (Or.inr (Or.inl hSz)) hlow hZ
  · exact false_of_rankOne (Or.inl hL2) hlow hZ
  · exact false_of_rankOne (Or.inr (Or.inr (Or.inr hSU3))) hlow hZ
  · refine hL3 n hSL3.2.admissible.2.1 ?_
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hSL3.2.card_eq_lieOrd (by norm_num)
  · refine hSp4 n hSp4'.admissible.2.1 ?_
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hSp4'.card_eq_lieOrd (by norm_num)

theorem card_eq_ordA_three_of_isSLn_four {X : Type} [Group X] {k : ℕ} (h : IsSLn X 4 k)
    (hk : 1 ≤ k) : Nat.card X = ordA 3 (2 ^ k) := by
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.ClassicalInvolution.Asc77.SCH.card_statedSL_four, hKcard,
    ← NoTransv.ordSL_four_two_pow_eq_ordA_three hk, CFSG.SeitzReduction.F4Pilot.ordSL_four]
  ring

theorem card_eq_ordA_three_of_isOmegaPlus_six {X : Type} [Group X] {k : ℕ}
    (h : IsOmegaPlus X 6 k) (hk : 2 ≤ k) : Nat.card X = ordA 3 (2 ^ k) := by
  obtain ⟨-, K, _, _, hKcard, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hv : ∃ v, CFSG.LieType.Universal.Spin.quadPlus 3 K v ≠ 0 := by
    let P := CFSG.ClassicalGroups.Orthogonal.plusPair K (⟨0, by norm_num⟩ : Fin 3)
    refine ⟨P.e + P.f, ?_⟩
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  rw [Nat.card_congr e.toEquiv, show (6 : ℕ) / 2 = 3 from rfl,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega
      (CFSG.LieType.Universal.Spin.coe_quadPlus 3 K) hv,
    CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadPlus_three h4, hKcard,
    NoTransv.ordSL_four_two_pow_eq_ordA_three (by omega)]

theorem card_eq_ordBC_three_of_isSpn_six {X : Type} [Group X] {k : ℕ} (h : IsSpn X 6 k)
    (hk : 1 ≤ k) : Nat.card X = ordBC 3 (2 ^ k) := by
  obtain ⟨-, K, _, _, hKcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, show (6 : ℕ) / 2 = 3 from rfl,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp 3, hKcard, ordBC,
    Nat.coprime_two_left.mpr (odd_two_pow_sub_one hk), Nat.div_one]
  norm_num

theorem card_eq_ordTwistedA_three_of_isSUn_four {X : Type} [Group X] {a : ℕ} (h : IsSUn X 4 a)
    (ha : 1 ≤ a) : Nat.card X = ordTwistedA 3 (2 ^ a) := by
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.ClassicalInvolution.Asc77.SCH.card_statedSU_four
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hKcard),
    ← NoTransv.ordSU_four_two_pow_eq_ordTwistedA_three ha, CFSG.SeitzReduction.F4Pilot.ordSU_four]
  ring

theorem card_eq_ordTwistedA_three_of_isOmegaMinus_six {X : Type} [Group X] {k : ℕ}
    (h : IsOmegaMinus X 6 k) (hk : 1 ≤ k) : Nat.card X = ordTwistedA 3 (2 ^ k) := by
  obtain ⟨-, K, _, _, b, c, hKcard, hirr, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have hv : ∃ v, CFSG.LieType.Universal.Spin.quadMinus 3 K b c v ≠ 0 := by
    let P := CFSG.ClassicalGroups.Orthogonal.minusPair K b c (⟨0, by norm_num⟩ : Fin (3 - 1))
    refine ⟨P.e + P.f, ?_⟩
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  rw [Nat.card_congr e.toEquiv, show (6 : ℕ) / 2 = 3 from rfl,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega
      (CFSG.LieType.Universal.Spin.coe_quadMinus 3 K b c) hv,
    CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_three hirr, hKcard,
    NoTransv.ordSU_four_two_pow_eq_ordTwistedA_three hk]

theorem not_nParamSingle_of_isSLn_four {X : Type} [Group X] {k n : ℕ} (h : IsSLn X 4 k)
    (hk : 2 ≤ k) : ¬ NParamSingle X n := by
  have hquot : Nat.card (X ⧸ Subgroup.center X) = ordA 3 (2 ^ k) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using
      (isLn_quot_center_of_isSLn h (by norm_num) (by omega)).card_eq_lieOrd (by norm_num)
  refine not_nParamSingle_of_lowOrder (lowOrder_of_isSLn_four (by omega) h)
    (fun _ => odd_card_center_of_isSLn h) (fun f hf hX => ?_) (fun f hf hX => ?_)
  · exact ordA_two_ne_ordA_three hf hk (hX.symm.trans hquot)
  · exact ordA_ne_ordBC_two (n := 3) (by norm_num) (by omega) hf
      ((card_eq_ordA_three_of_isSLn_four h (by omega)).symm.trans hX)

theorem not_nParamSingle_of_isOmegaPlus_six {X : Type} [Group X] {k n : ℕ}
    (h : IsOmegaPlus X 6 k) (hk : 2 ≤ k) : ¬ NParamSingle X n := by
  have := isSimpleGroup_of_isOmegaPlus_six h
  have hcard := card_eq_ordA_three_of_isOmegaPlus_six h hk
  have hquot : Nat.card (X ⧸ Subgroup.center X) = ordA 3 (2 ^ k) :=
    (card_quot_center_of_isSimpleGroup (isQuasisimple_of_isOmegaPlus_six h)).trans hcard
  refine not_nParamSingle_of_lowOrder (lowOrder_of_isOmegaPlus_six hk h)
    (fun hq => odd_card_center_of_isSimpleGroup inferInstance hq) (fun f hf hX => ?_)
    (fun f hf hX => ?_)
  · exact ordA_two_ne_ordA_three hf hk (hX.symm.trans hquot)
  · exact ordA_ne_ordBC_two (n := 3) (by norm_num) (by omega) hf (hcard.symm.trans hX)

theorem not_nParamSingle_of_isSpn_six {X : Type} [Group X] {k n : ℕ} (h : IsSpn X 6 k)
    (hk : 1 ≤ k) : ¬ NParamSingle X n := by
  have hquot : Nat.card (X ⧸ Subgroup.center X) = ordBC 3 (2 ^ k) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using
      (lieModel_quot_center_of_isSpn (m := 3) h le_rfl hk).card_eq_lieOrd (by norm_num)
  refine not_nParamSingle_of_lowOrder (lowOrder_of_isSpn_six hk h)
    (fun _ => odd_card_center_of_isSpn h) (fun f hf hX => ?_) (fun f hf hX => ?_)
  · exact ordA_two_ne_ordBC_three hf hk (hX.symm.trans hquot)
  · exact ordBC_ne_ordBC_two (n := 3) le_rfl hk hf
      ((card_eq_ordBC_three_of_isSpn_six h hk).symm.trans hX)

theorem not_nParamSingle_of_isSUn_four {X : Type} [Group X] {a n : ℕ} (h : IsSUn X 4 a)
    (ha : 1 ≤ a) : ¬ NParamSingle X n := by
  have hquot : Nat.card (X ⧸ Subgroup.center X) = ordTwistedA 3 (2 ^ a) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using
      (isU4_quot_center_of_isSUn_four h ha).card_eq_lieOrd (by norm_num)
  refine not_nParamSingle_of_lowOrder (lowOrder_of_isSUn_four ha h)
    (fun _ => odd_card_center_of_isSUn_four h) (fun f hf hX => ?_) (fun f hf hX => ?_)
  · exact ordA_ne_ordTwistedA (n := 2) (by norm_num) hf (by norm_num) ha (hX.symm.trans hquot)
  · exact ordBC_two_ne_ordTwistedA hf (by norm_num) ha
      (hX.symm.trans (card_eq_ordTwistedA_three_of_isSUn_four h ha))

theorem not_nParamSingle_of_isOmegaMinus_six {X : Type} [Group X] {k n : ℕ}
    (h : IsOmegaMinus X 6 k) (hk : 1 ≤ k) : ¬ NParamSingle X n := by
  have := isSimpleGroup_of_isOmegaMinus_six h
  have hcard := card_eq_ordTwistedA_three_of_isOmegaMinus_six h hk
  have hquot : Nat.card (X ⧸ Subgroup.center X) = ordTwistedA 3 (2 ^ k) :=
    (card_quot_center_of_isSimpleGroup (isQuasisimple_of_isOmegaMinus h (by norm_num))).trans hcard
  refine not_nParamSingle_of_lowOrder (lowOrder_of_isOmegaMinus_six hk h)
    (fun hq => odd_card_center_of_isSimpleGroup inferInstance hq) (fun f hf hX => ?_)
    (fun f hf hX => ?_)
  · exact ordA_ne_ordTwistedA (n := 2) (by norm_num) hf (by norm_num) hk (hX.symm.trans hquot)
  · exact ordBC_two_ne_ordTwistedA hf (by norm_num) hk (hX.symm.trans hcard)

theorem not_nParamSingle_of_isOmega8m {X : Type} [Group X] {k n : ℕ} (h : IsOmega8m X k) :
    ¬ NParamSingle X n := by
  have : IsSimpleGroup X :=
    LieModel.isSimpleGroup_of_mem_classicalTags (t := .POmegaMinus) (by decide) h
  have hk : 1 ≤ k := h.admissible.2.1
  have hcard : Nat.card X = ordTwistedD 4 (2 ^ k) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  have hquot : Nat.card (X ⧸ Subgroup.center X) = ordTwistedD 4 (2 ^ k) :=
    (card_quot_center_of_isSimpleGroup (isQuasisimple_of_isOmega8m h)).trans hcard
  refine not_nParamSingle_of_lowOrder (lowOrder_of_isOmega8m h)
    (fun hq => odd_card_center_of_isSimpleGroup inferInstance hq) (fun f hf hX => ?_)
    (fun f hf hX => ?_)
  · exact ordA_two_ne_ordTwistedD_four hf hk (hX.symm.trans hquot)
  · exact ordTwistedD_ne_ordBC_two (n := 4) le_rfl hk hf (hcard.symm.trans hX)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_nParam_of_isSLn_four {k n : ℕ} (h : IsSLn (Bar2 L) 4 k) (hk : 2 ≤ k) :
    ¬ NParam L n := fun hN => not_nParamSingle_of_isSLn_four h hk
  (nParamSingle_of_nParam_of_isQuasisimple hN (isQuasisimple_of_isSLn (by norm_num) h hk))

theorem not_nParam_of_isOmegaPlus_six {k n : ℕ} (h : IsOmegaPlus (Bar2 L) 6 k) (hk : 2 ≤ k) :
    ¬ NParam L n := fun hN => not_nParamSingle_of_isOmegaPlus_six h hk
  (nParamSingle_of_nParam_of_isQuasisimple hN (isQuasisimple_of_isOmegaPlus_six h))

theorem not_nParam_of_isSpn_six {k n : ℕ} (h : IsSpn (Bar2 L) 6 k) (hk : 2 ≤ k) :
    ¬ NParam L n := fun hN => not_nParamSingle_of_isSpn_six h (by omega)
  (nParamSingle_of_nParam_of_isQuasisimple hN (isQuasisimple_of_isSpn_six h hk))

theorem not_nParam_of_isSUn_four {a n : ℕ} (h : IsSUn (Bar2 L) 4 a) (ha : 1 ≤ a) :
    ¬ NParam L n := fun hN => not_nParamSingle_of_isSUn_four h ha
  (nParamSingle_of_nParam_of_isQuasisimple hN (isQuasisimple_of_isSUn_four h))

theorem not_nParam_of_isOmegaMinus_six {k n : ℕ} (h : IsOmegaMinus (Bar2 L) 6 k) (hk : 1 ≤ k) :
    ¬ NParam L n := fun hN => not_nParamSingle_of_isOmegaMinus_six h hk
  (nParamSingle_of_nParam_of_isQuasisimple hN (isQuasisimple_of_isOmegaMinus h (by norm_num)))

theorem not_nParam_of_isOmega8m {k n : ℕ} (h : IsOmega8m (Bar2 L) k) : ¬ NParam L n :=
  fun hN => not_nParamSingle_of_isOmega8m h
    (nParamSingle_of_nParam_of_isQuasisimple hN (isQuasisimple_of_isOmega8m h))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
