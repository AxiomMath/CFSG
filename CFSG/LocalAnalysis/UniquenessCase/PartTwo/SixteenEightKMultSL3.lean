module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.GH74.Generic.GKFCover
public import CFSG.Open.StatedCenterThree
public import CFSG.Adapters.StatedSLPerfect
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.CoverOdd
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open CFSG.RankThree.PerfectCover

theorem s16k_card_mul_card_ker_dvd_griess {X S : Type} [Group X] [Finite X] [Group S]
    (hX : Group.IsPerfect X) (π : X →* S) (hπ : Function.Surjective π)
    (hk : π.ker ≤ Subgroup.center X) :
    Nat.card (griessHopfMultiplier X) * Nat.card π.ker ∣ Nat.card (griessHopfMultiplier S) := by
  haveI : Finite S := Finite.of_surjective π hπ
  haveI : Nonempty S := ⟨1⟩
  haveI : Group.IsPerfect X := hX
  let E := HopfCover X
  haveI : Finite E := finite_hopfCover hX
  haveI : Group.IsPerfect E := hopfCover_isPerfect
  let q : E →* S := π.comp (hopfCoverMap X)
  have hq : Function.Surjective q := hπ.comp (hopfCoverMap_surjective (S := X))
  have hkq : q.ker ≤ Subgroup.center E := by
    intro t ht
    have h2 : t ∈ Subgroup.upperCentralSeries E (1 + 1) := by
      rw [Subgroup.mem_upperCentralSeries_succ_iff]
      intro y
      rw [Subgroup.upperCentralSeries_one]
      apply hopfMultiplier_le_center (S := X)
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have hta : hopfCoverMap X t ∈ Subgroup.center X := by
        apply hk
        rw [MonoidHom.mem_ker]
        simpa only [q, MonoidHom.comp_apply] using MonoidHom.mem_ker.mp ht
      exact commutatorElement_eq_one_iff_commute.mpr
        (Subgroup.mem_center_iff.mp hta (hopfCoverMap X y)).symm
    rwa [Group.IsPerfect.upperCentralSeries_eq_center E (by norm_num : 1 + 1 ≠ 0)] at h2
  have hdvd : Nat.card q.ker ∣ Nat.card (hopfMultiplier S) :=
    CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier (hopfCover_isPerfect (S := X)) q hq hkq
  have hcard1 : Nat.card E = Nat.card X * Nat.card (hopfMultiplier X) :=
    CFSG.GH74.Generic.card_eq_card_mul_card_ker (hopfCoverMap X)
      (hopfCoverMap_surjective (S := X))
  have hcard2 : Nat.card X = Nat.card S * Nat.card π.ker :=
    CFSG.GH74.Generic.card_eq_card_mul_card_ker π hπ
  have hcard3 : Nat.card E = Nat.card S * Nat.card q.ker :=
    CFSG.GH74.Generic.card_eq_card_mul_card_ker q hq
  have hcancel : Nat.card q.ker = Nat.card π.ker * Nat.card (hopfMultiplier X) := by
    have h : Nat.card S * Nat.card q.ker =
        Nat.card S * (Nat.card π.ker * Nat.card (hopfMultiplier X)) := by
      rw [hcard3.symm, hcard1, hcard2, mul_assoc]
    exact Nat.mul_left_cancel (Nat.card_pos) h
  have hgoal : Nat.card (hopfMultiplier X) * Nat.card π.ker ∣ Nat.card (hopfMultiplier S) := by
    have hqk : Nat.card (hopfMultiplier X) * Nat.card π.ker = Nat.card q.ker := by
      rw [hcancel]
      exact Nat.mul_comm _ _
    rw [hqk]
    exact hdvd
  rwa [Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv,
    Nat.card_congr (hopfMultiplierEquivGriess S).toEquiv]

theorem s16k_mult_sl3_four (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] (h : IsSLn X 3 2) :
    Nat.card (Subgroup.center X) = 3 ∧ Nat.card (CFSG.Open.griessHopfMultiplier X) ∣ 16 := by
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  haveI : Finite (StatedSL 3 K) := Finite.of_surjective e e.surjective
  have hcenter : Nat.card (Subgroup.center X) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.Open.StatedCenterThree.card_center_statedSL_three (K := K)
      (by norm_num [hK4])
  let N : Subgroup (StatedSL 3 K) := (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)
  let S : Type := StatedProj (StatedSL 3 K)
  let π : StatedSL 3 K →* S := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hN : N = Subgroup.center (StatedSL 3 K) :=
    (CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.center_statedSL_eq_scalars
      K).symm
  have hk : π.ker ≤ Subgroup.center (StatedSL 3 K) := by rw [hker, hN]
  have hperf : Group.IsPerfect (StatedSL 3 K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num : 3 ≤ 3) K
  have hmain := s16k_card_mul_card_ker_dvd_griess hperf π hπ hk
  have hker3 : Nat.card π.ker = 3 := by
    rw [hker, hN]
    exact CFSG.Open.StatedCenterThree.card_center_statedSL_three (K := K)
      (by norm_num [hK4])
  have hadm : StatedLieAdmissible .PSL 3 2 2 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  have hmodel : CFSG.Models.LieModel S .PSL 3 2 2 :=
    ⟨hadm, Or.inl ⟨hadm, K, hKfield, hKfinite, hKcard, ⟨MulEquiv.refl _⟩⟩⟩
  obtain ⟨-, ⟨m⟩⟩ := hGA S .PSL 3 2 2 hmodel
  have hS48 : Nat.card (griessHopfMultiplier S) = 48 := by
    rw [Nat.card_congr m.toEquiv]
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
      CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
      Nat.card_prod]
    norm_num [ZMod.card, Nat.card_eq_fintype_card]
  have hdvd48 := hmain
  rw [hker3, hS48] at hdvd48
  rw [show (48 : ℕ) = 16 * 3 by norm_num] at hdvd48
  have hdvd16 : Nat.card (griessHopfMultiplier (StatedSL 3 K)) ∣ 16 :=
    Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 3) hdvd48
  refine ⟨hcenter, ?_⟩
  rwa [Nat.card_congr
    (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
