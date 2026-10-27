module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ShultStronglyClosedTI

universe u

variable {G : Type u} [Group G]

section Sylow

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem card_sylow_map {K : Subgroup G} (S : Sylow p K) :
    Nat.card ((S : Subgroup K).map K.subtype) = p ^ (Nat.card K).factorization p := by
  rw [Subgroup.card_map_of_injective K.subtype_injective, S.card_eq_multiplicity]

theorem exists_sylow_map_eq_of_card {K P : Subgroup G} (hPK : P ≤ K)
    (hcard : Nat.card P = p ^ (Nat.card K).factorization p) :
    ∃ S : Sylow p K, (S : Subgroup K).map K.subtype = P := by
  have hcard' : Nat.card (P.subgroupOf K) = p ^ (Nat.card K).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hcard]
  exact ⟨Sylow.ofCard _ hcard', by
    rw [Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype, inf_of_le_left hPK]⟩

theorem card_eq_pow_factorization_of_le {P K C : Subgroup G} (hPK : P ≤ K) (hKC : K ≤ C)
    (hcard : Nat.card P = p ^ (Nat.card C).factorization p) :
    Nat.card P = p ^ (Nat.card K).factorization p := by
  have hp : p.Prime := Fact.out
  have h1 : (Nat.card K).factorization p ≤ (Nat.card C).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_dvd_of_le hKC) p
  have h2 : (Nat.card C).factorization p ≤ (Nat.card K).factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization Nat.card_pos.ne', ← hcard]
    exact Subgroup.card_dvd_of_le hPK
  rw [hcard, le_antisymm h1 h2]

omit [Finite G] [Fact p.Prime] in
theorem mem_sylow_map_of_central {K : Subgroup G} {y : G} (hyK : y ∈ K)
    (hcentral : ∀ k ∈ K, k * y = y * k) (hy : orderOf y = p) (S : Sylow p K) :
    y ∈ (S : Subgroup K).map K.subtype := by
  let yK : K := ⟨y, hyK⟩
  have hnormal : (Subgroup.zpowers yK).Normal := by
    constructor
    intro n hn g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hcomm : g * yK = yK * g := Subtype.ext (hcentral g g.2)
    have hconj : g * yK ^ k * g⁻¹ = yK ^ k := by
      rw [((Commute.zpow_right (show Commute g yK from hcomm) k)).eq, mul_inv_cancel_right]
    rw [hconj]
    exact Subgroup.zpow_mem_zpowers yK k
  have hpgroup : IsPGroup p (Subgroup.zpowers yK) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk, hy]
  have hle := hpgroup.le_sylow_of_normal S
  exact Subgroup.mem_map.mpr ⟨yK, hle (Subgroup.mem_zpowers yK), rfl⟩

end Sylow

theorem mem_pointFixedSet_map_conj (H P : Subgroup G) (g : G) (ω : rightCosetSpace H) :
    ω ∈ pointFixedSet H (P.map (MulAut.conj g).toMonoidHom) ↔
      rightCosetTranslate H ω g ∈ pointFixedSet H P := by
  constructor
  · intro hω q hq
    have hfix := hω (g * q * g⁻¹) (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩)
    rw [pointRightCosetMul_eq_translate] at hfix ⊢
    have heq : g * q = (g * q * g⁻¹) * g := by group
    rw [rightCosetTranslate_mul, heq, ← rightCosetTranslate_mul, hfix]
  · intro hω x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    have hfix := hω q hq
    rw [pointRightCosetMul_eq_translate] at hfix ⊢
    change rightCosetTranslate H ω (g * q * g⁻¹) = ω
    rw [← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hfix, rightCosetTranslate_mul,
      mul_inv_cancel, rightCosetTranslate_one]

theorem centralizer_conj_eq_map (y g : G) :
    Subgroup.centralizer ({g * y * g⁻¹} : Set G) =
      (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * x * g * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * x) * g := by rw [hx]
        _ = y * (g⁻¹ * x * g) := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · intro hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hw
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * w * g⁻¹ * (g * y * g⁻¹) = g * (w * y) * g⁻¹ := by group
      _ = g * (y * w) * g⁻¹ := by rw [hw]
      _ = g * y * g⁻¹ * (g * w * g⁻¹) := by group

theorem exists_mem_ne_one_of_one_lt_card {E : Subgroup G} (hE : 1 < Nat.card E) :
    ∃ r ∈ E, r ≠ 1 := by
  by_contra hnone
  push Not at hnone
  have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hnone
  rw [hbot, Subgroup.card_bot] at hE
  exact lt_irrefl 1 hE

theorem isPGroup_two_of_isElemAbelian {Q : Subgroup G} (hQ : CFSG.Open.IsElemAbelian 2 Q) :
    IsPGroup 2 Q := CFSG.Open.IsElemAbelian.isPGroup hQ

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
