module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverAbstract
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise

variable {X : Type*} [Group X] [Finite X]

theorem uc22ine229_card_sylow_dvd_index {H : Subgroup X} (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    {r : ℕ} [Fact r.Prime] (hr : ¬ r ∣ H.index) : Nat.card (Sylow r X) ∣ H.index := by
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow r H))
  have hP : IsPGroup r ((P₀ : Subgroup H).map H.subtype) := P₀.isPGroup'.map _
  have hPi : ¬ r ∣ ((P₀ : Subgroup H).map H.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact fun h => ((Nat.Prime.dvd_mul Fact.out).1 h).elim P₀.not_dvd_index hr
  rw [(hP.toSylow hPi).card_eq_index_normalizer]
  refine Subgroup.index_dvd_of_le fun h hh => mem_normalizer_fintype fun x hx => ?_
  rw [SetLike.mem_coe, IsPGroup.mem_toSylow] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Subgroup.coe_subtype, hH h hh _ y.2, mul_inv_cancel_right]
  exact ⟨y, hy, rfl⟩

theorem uc22ine229_exists_sylow_le_normalizer {p q : ℕ} (hp : p.Prime) [Fact q.Prime]
    {W A : Subgroup X} (hA : IsPGroup p A) (hAW : A ≤ normalizer (W : Set X))
    (hcard : ¬ p ∣ Nat.card (Sylow q W)) :
    ∃ S : Sylow q W, A ≤ normalizer (((S : Subgroup W).map W.subtype : Subgroup X) : Set X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulDistribMulAction ↥A ↥W := Subgroup.conjMulDistribMulActionOfLeNormalizer A W hAW
  letI : MulAction ↥A (Sylow q W) := Sylow.pointwiseMulAction
  obtain ⟨S, hS⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q W) hcard
  refine ⟨S, fun a ha => ?_⟩
  have hfix : (⟨a, ha⟩ : ↥A) • (S : Subgroup ↥W) = S := by
    rw [← Sylow.pointwise_smul_def]
    exact congrArg Sylow.toSubgroup (hS ⟨a, ha⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : (⟨a, ha⟩ : ↥A) • s ∈ (S : Subgroup ↥W) :=
      hfix ▸ Subgroup.smul_mem_pointwise_smul s (⟨a, ha⟩ : ↥A) (S : Subgroup ↥W) hs
    exact ⟨(⟨a, ha⟩ : ↥A) • s, hs', rfl⟩
  · rintro ⟨s', hs', hs'x⟩
    rw [← hfix] at hs'
    obtain ⟨s, hs, rfl⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists s' (⟨a, ha⟩ : ↥A) (S : Subgroup ↥W)).1 hs'
    refine ⟨s, hs, ?_⟩
    have h1 : a * (s : X) * a⁻¹ = a * x * a⁻¹ := hs'x
    simpa using h1

theorem uc22ine229_exists_orderOf_le_normalizer {W A : Subgroup X} {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hrk : CFSG.Open.pRank r W ≤ 1) (hrW : r ∣ Nat.card W)
    (hs : ¬ p ∣ Nat.card (Sylow r W)) (hA : IsPGroup p A) (hAW : A ≤ normalizer (W : Set X)) :
    ∃ y ∈ W, orderOf y = r ∧ A ≤ normalizer (zpowers y : Set X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨S, hS⟩ := uc22ine229_exists_sylow_le_normalizer hp hA hAW hs
  have hrS : r ∣ Nat.card (S : Subgroup W) := by
    rw [← (S : Subgroup W).card_mul_index] at hrW
    exact ((Nat.Prime.dvd_mul hr).1 hrW).resolve_right S.not_dvd_index
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hrS
  have hyo : orderOf ((y : W) : X) = r := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  have hyS : ((y : W) : X) ∈ (S : Subgroup W).map W.subtype := ⟨y, y.2, rfl⟩
  have hSp : IsPGroup r ((S : Subgroup W).map W.subtype) := S.isPGroup'.map _
  refine ⟨(y : W), (y : W).2, hyo, fun a ha => mem_normalizer_fintype fun z hz => ?_⟩
  have hzS := hyS
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
  have hmem : a * ((y : W) : X) * a⁻¹ ∈ (S : Subgroup W).map W.subtype :=
    (mem_normalizer_iff.1 (hS ha) _).1 hyS
  rw [← conj_zpow]
  refine zpow_mem ?_ k
  have hco : orderOf (a * ((y : W) : X) * a⁻¹) = r :=
    (SemiconjBy.orderOf_eq a (by rw [SemiconjBy]; group)).symm.trans hyo
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPCov.mem_zpowers_of_isPGroup_pRank_le_one
    hrk hSp (map_subtype_le _) hzS hmem hyo hco

end CFSG.LocalAnalysis.UniquenessCase.UC22
