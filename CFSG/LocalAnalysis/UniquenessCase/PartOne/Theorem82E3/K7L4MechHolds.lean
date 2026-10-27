module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLie
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.K7L4MechModel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6rL4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Realize
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4RankQModel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelTransport
import CFSG.GroupTheory.WeirSylow.UniqueE27GLFour
import CFSG.GroupTheory.WeirSylow.UniqueE27LinearFour
import CFSG.GroupTheory.WeirSylow.UniqueE27UnitaryFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (IsLie811 qPlusPi center_eq_bot_of_isLie811_of_ne exists_equiv_statedProj_of_isLie811_l4)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelTransport
open CFSG.GroupTheory.WeirSylow

private theorem k7L4Mech_sl_second {Y : Type} [Group Y] [Finite Y] {f : ℕ} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) (ζ : CubeRoot K)
    (hD : D₀ ζ ≤ StatedSL 4 K)
    (hU : CFSG.GroupTheory.UniqueElemSylow 3 3 (StatedProj (StatedSL 4 K)))
    (e : Y ⧸ center Y ≃* StatedProj (StatedSL 4 K)) (hZ : center Y = ⊥)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
      p ∣ Nat.card (centralizer (X : Set Y)) := by
  intro X hXA hX3
  have hroot : ∀ S : Set (Multiplicative (Fin 4 → ZMod 3)),
      ((∀ v ∈ S, Multiplicative.toAdd v 2 = Multiplicative.toAdd v 3) ∨
        ∀ v ∈ S, Multiplicative.toAdd v 0 = Multiplicative.toAdd v 1) →
      1 ≤ CFSG.Open.pRank p (Subgroup.centralizer (stdDiagHomH ζ hD '' S)) := by
    intro S hS
    rcases hS with hS | hS
    · exact one_le_pRank_centralizer_stdDiagHomH_sl23 hp hK hpq ζ hD S hS
    · exact one_le_pRank_centralizer_stdDiagHomH_sl01 hp hK hpq ζ hD S hS
  have h := (forall_le_pRank_centralizer_of_stdDiag_model
    (H := StatedSL 4 K)
    (fun c hc => scalar_pow_four_eq_one_of_mem_statedSL hc) hD
    (isSumZeroCoords_statedSL ζ) hU
    (center Y) hZ e (r := p) (f := 1) hp (by omega) hroot hA h27).1 X hXA hX3
  exact CFSG.GroupTheory.dvd_card_of_one_le_pRank hp h

private theorem k7L4Mech_su_second {Y : Type} [Group Y] [Finite Y] {f : ℕ} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) (hq3 : 3 ∣ 2 ^ f + 1)
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K) (ζ : CubeRoot K)
    (hD : D₀ ζ ≤ StatedSU 4 (2 ^ f) K)
    (hUS : CFSG.GroupTheory.UniqueElemSylow 3 3 (StatedProj (StatedSU 4 (2 ^ f) K)))
    (e : Y ⧸ center Y ≃* StatedProj (StatedSU 4 (2 ^ f) K)) (hZ : center Y = ⊥)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f - 1)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
      p ∣ Nat.card (centralizer (X : Set Y)) := by
  intro X hXA hX3
  have hroot : ∀ S : Set (Multiplicative (Fin 4 → ZMod 3)),
      ((∀ v ∈ S, Multiplicative.toAdd v 2 = Multiplicative.toAdd v 3) ∨
        ∀ v ∈ S, Multiplicative.toAdd v 0 = Multiplicative.toAdd v 1) →
      1 ≤ CFSG.Open.pRank p (Subgroup.centralizer (stdDiagHomH ζ hD '' S)) := by
    intro S hS
    rcases hS with hS | hS
    · exact one_le_pRank_centralizer_stdDiagHomH_su23 hU hp hpq ζ hD S hS
    · exact one_le_pRank_centralizer_stdDiagHomH_su01 hU hp hpq ζ hD S hS
  have h := (forall_le_pRank_centralizer_of_stdDiag_model
    (H := StatedSU 4 (2 ^ f) K)
    (fun c hc => scalar_pow_four_eq_one_of_mem_statedSL
      (CFSG.Open.StatedAPI.statedSU_le_statedSL 4 (2 ^ f) K hc)) hD
    (isSumZeroCoords_statedSU (neg_one_pow_eq_neg_one_of_card_eq_sq hK) hq3 ζ)
    hUS (center Y) hZ e (r := p) (f := 1) hp (by omega) hroot hA h27).1 X hXA hX3
  exact CFSG.GroupTheory.dvd_card_of_one_le_pRank hp h

private theorem k7L4Mech_sl {Y : Type} [Group Y] [Finite Y] {f : ℕ} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) (hmod : 2 ^ f % 3 = 1)
    (e : Y ⧸ center Y ≃* StatedProj (StatedSL 4 K)) (hZ : center Y = ⊥)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ¬ p ∣ Nat.card (centralizer (A : Set Y)) ∧
      ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
        p ∣ Nat.card (centralizer (X : Set Y)) := by
  have h3 : 3 ∣ Nat.card K - 1 := by rw [hK]; omega
  obtain ⟨ζ⟩ := CubeRoot.exists_of_dvd h3
  have hD : D₀ ζ ≤ StatedSL 4 K := d₀_le_sl ζ
  haveI : Fact p.Prime := ⟨hp⟩
  have hU := uniqueElemSylow_statedProj_statedSL_four h3
  refine ⟨?_, ?_⟩
  · refine not_dvd_card_centralizer_of_model
      (H := StatedSL 4 K) (N := (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K))
      (Z := center Y) (hU := ?_) (hN := ?_) (hZ := ?_) (hNℓ := ?_) (hZℓ := ?_)
      (e := e) (A₀ := (D₀ ζ).subgroupOf (StatedSL 4 K)) ?_ ?_ ?_ hA h27
    · exact hU
    · exact CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
        (M := StatedSL 4 K) (d := 4) (p := 3) Nat.prime_three (by norm_num)
        (fun c hc => scalar_pow_four_eq_one_of_mem_statedSL hc)
    · rw [hZ, Subgroup.card_bot]; norm_num
    · exact CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
        (M := StatedSL 4 K) (d := 4) (p := p) hp
        (Nat.not_dvd_of_pos_of_lt (n := 4) (m := p) (by norm_num) (by omega))
        (fun c hc => scalar_pow_four_eq_one_of_mem_statedSL hc)
    · rw [hZ, Subgroup.card_bot]; exact fun h => hp.ne_one (Nat.dvd_one.mp h)
    · exact (isElemAbelian_D₀ ζ).subgroupOf (StatedSL 4 K)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv, card_D₀ ζ]
    · exact not_dvd_card_centralizer_D0_sl hp hp5 hK hpq ζ hD
  · exact k7L4Mech_sl_second hK ζ hD hU e hZ hp hp5 hpq hA h27

private theorem k7L4Mech_su {Y : Type} [Group Y] [Finite Y] {f : ℕ} {K : Type}
    [Field K] [Finite K] (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hmod : 2 ^ f % 3 = 2) (e : Y ⧸ center Y ≃* StatedProj (StatedSU 4 (2 ^ f) K))
    (hZ : center Y = ⊥) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f - 1)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ¬ p ∣ Nat.card (centralizer (A : Set Y)) ∧
      ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
        p ∣ Nat.card (centralizer (X : Set Y)) := by
  have hq3 : 3 ∣ 2 ^ f + 1 := by omega
  have hd : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have hsq : (2 ^ f) ^ 2 - 1 = ((2 ^ f) + 1) * ((2 ^ f) - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ f) 1
    rw [hsq]
    exact dvd_mul_of_dvd_left hq3 _
  obtain ⟨ζ⟩ := CubeRoot.exists_of_dvd hd
  have hD : D₀ ζ ≤ StatedSU 4 (2 ^ f) K := d₀_le_statedSU hq3 ζ
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, Nat.mul_comm f 2]⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hUS := uniqueElemSylow_statedProj_statedSU_four hK hq3
  refine ⟨?_, ?_⟩
  · refine not_dvd_card_centralizer_of_model
      (H := StatedSU 4 (2 ^ f) K)
      (N := (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ f) K))
      (Z := center Y) (hU := ?_) (hN := ?_) (hZ := ?_) (hNℓ := ?_) (hZℓ := ?_)
      (e := e) (A₀ := (D₀ ζ).subgroupOf (StatedSU 4 (2 ^ f) K)) ?_ ?_ ?_ hA h27
    · exact hUS
    · exact CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
        (M := StatedSU 4 (2 ^ f) K) (d := 4) (p := 3) Nat.prime_three (by norm_num)
        (fun c hc => scalar_pow_four_eq_one_of_mem_statedSL
          (CFSG.Open.StatedAPI.statedSU_le_statedSL 4 (2 ^ f) K hc))
    · rw [hZ, Subgroup.card_bot]; norm_num
    · exact CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
        (M := StatedSU 4 (2 ^ f) K) (d := 4) (p := p) hp
        (Nat.not_dvd_of_pos_of_lt (n := 4) (m := p) (by norm_num) (by omega))
        (fun c hc => scalar_pow_four_eq_one_of_mem_statedSL
          (CFSG.Open.StatedAPI.statedSU_le_statedSL 4 (2 ^ f) K hc))
    · rw [hZ, Subgroup.card_bot]; exact fun h => hp.ne_one (Nat.dvd_one.mp h)
    · exact (isElemAbelian_D₀ ζ).subgroupOf (StatedSU 4 (2 ^ f) K)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv, card_D₀ ζ]
    · exact not_dvd_card_centralizer_D0_su hU hp hp5 hpq ζ hD
  · exact k7L4Mech_su_second hK hq3 hU ζ hD hUS e hZ hp hp5 hpq hA h27

theorem k7L4Mech_holds :
    K7L4Mech := by
  intro Y _ _ f hY p hp hp5 hpq A hA h27
  have hZ : center Y = ⊥ :=
    center_eq_bot_of_isLie811_of_ne hY (by decide) (fun h => absurd h (by decide))
  obtain ⟨-, hf, ⟨K, _, _, hK, hmod, ⟨e⟩⟩ | ⟨K, _, _, hK, hmod, ⟨e⟩⟩⟩ :=
    exists_equiv_statedProj_of_isLie811_l4 hY
  · have hpq' : p ∣ 2 ^ f + 1 := by
      rw [qPlusPi, if_pos hmod] at hpq
      exact hpq
    exact k7L4Mech_sl hK hmod e hZ hp hp5 hpq' hA h27
  · have hpq' : p ∣ 2 ^ f - 1 := by
      rw [qPlusPi, if_neg (by omega : ¬ 2 ^ f % 3 = 1)] at hpq
      exact hpq
    exact k7L4Mech_su hf hK hmod e hZ hp hp5 hpq' hA h27

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
