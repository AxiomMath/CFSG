module

import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Blueprint.Catalog
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)

open scoped commutatorElement

private theorem k329n19_simple_subgroupOf {G : Type} [Group G] {X K : Subgroup G}
    (hXK : X ≤ K) (h : LieModel ↥X .PSU 3 2 3) :
    IsSimpleGroup ↥(X.subgroupOf K) :=
  @MulEquiv.isSimpleGroup ↥(X.subgroupOf K) _ ↥X _
    (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h)
    (Subgroup.subgroupOfEquivOfLe hXK)

private theorem k329n19_card_subgroupOf {G : Type} [Group G] {X K : Subgroup G}
    (hXK : X ≤ K) (h : LieModel ↥X .PSU 3 2 3) :
    Nat.card ↥(X.subgroupOf K) = 5515776 := by
  calc Nat.card ↥(X.subgroupOf K) = Nat.card ↥X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv
    _ = 5515776 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight
        (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

private theorem k329n19_not_commutative {G : Type} [Group G] {X K : Subgroup G}
    (hXK : X ≤ K) (h : LieModel ↥X .PSU 3 2 3) :
    ¬ IsMulCommutative ↥(X.subgroupOf K) := by
  intro hcomm
  have hsimple : IsSimpleGroup ↥(X.subgroupOf K) := k329n19_simple_subgroupOf hXK h
  have hprime : (Nat.card ↥(X.subgroupOf K)).Prime :=
    (@Group.is_simple_iff_prime_card ↥(X.subgroupOf K) _ hcomm).mp hsimple
  rw [k329n19_card_subgroupOf hXK h] at hprime
  exact (by norm_num : ¬ (5515776 : ℕ).Prime) hprime

private theorem k329n19_center_subgroupOf_eq_bot {G : Type} [Group G] {X K : Subgroup G}
    (hXK : X ≤ K) (h : LieModel ↥X .PSU 3 2 3) :
    (Subgroup.center ↥K).subgroupOf (X.subgroupOf K) = ⊥ := by
  have hsimple : IsSimpleGroup ↥(X.subgroupOf K) := k329n19_simple_subgroupOf hXK h
  rcases hsimple.eq_bot_or_eq_top_of_normal
      ((Subgroup.center ↥K).subgroupOf (X.subgroupOf K)) with hbot | htop
  · exact hbot
  · exfalso
    refine k329n19_not_commutative hXK h (IsMulCommutative.of_comm fun a b => ?_)
    have ha : (a : ↥K) ∈ Subgroup.center ↥K := by
      apply Subgroup.mem_subgroupOf.mp
      rw [htop]
      exact Set.mem_univ a
    exact Subtype.ext (Subgroup.mem_center_iff.mp ha (b : ↥K)).symm

theorem k329_nineteen_dvd :
    ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G), X ≤ CFSG.Open.genFittingFStar G →
      LieModel ↥X .PSU 3 2 3 →
      19 ∣ Nat.card (↥(CFSG.Open.genFittingFStar G) ⧸
        Subgroup.center ↥(CFSG.Open.genFittingFStar G)) := by
  intro G _ _ X hXK h
  set K : Subgroup G := CFSG.Open.genFittingFStar G with hK
  set X' : Subgroup ↥K := X.subgroupOf K with hX'
  set Z : Subgroup ↥K := Subgroup.center ↥K with hZ
  have hker : MonoidHom.ker ((QuotientGroup.mk' Z).comp X'.subtype) = ⊥ := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_subtype]
    exact k329n19_center_subgroupOf_eq_bot hXK h
  have hinj : Function.Injective ((QuotientGroup.mk' Z).comp X'.subtype) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hdvd : Nat.card ↥X' ∣ Nat.card (↥K ⧸ Z) :=
    Subgroup.card_dvd_of_injective _ hinj
  have hcard : Nat.card ↥X' = 5515776 := k329n19_card_subgroupOf hXK h
  exact dvd_trans (by norm_num : (19 : ℕ) ∣ 5515776) (hcard ▸ hdvd)

private theorem k329eu_simple_subgroupOf {G : Type*} [Group G] {K X : Subgroup G}
    (hXK : X ≤ K) (h : IsSimpleGroup ↥X) : IsSimpleGroup ↥(X.subgroupOf K) := by
  have : IsSimpleGroup ↥X := h
  exact (Subgroup.subgroupOfEquivOfLe hXK).isSimpleGroup

private theorem k329eu_inf_center_eq_bot {L : Type*} [Group L] (X' : Subgroup L)
    (hcard : Nat.card ↥X' = 5515776) (hsimp : IsSimpleGroup ↥X') :
    X' ⊓ Subgroup.center L = ⊥ := by
  rcases (Subgroup.isSimpleGroup_iff.mp hsimp).2 (X' ⊓ Subgroup.center L) inf_le_left
      (by
        rw [Subgroup.inf_subgroupOf_left]
        infer_instance)
    with h | h
  · exact h
  · exfalso
    have hle : X' ≤ Subgroup.center L := by
      rw [← h]
      exact inf_le_right
    have : IsMulCommutative ↥X' :=
      IsMulCommutative.of_comm fun a b => Subtype.ext (by
        exact (Subgroup.mem_center_iff.mp (hle a.2) b).symm)
    have hp : Nat.Prime (Nat.card ↥X') := Group.is_simple_iff_prime_card.mp hsimp
    rw [hcard] at hp
    exact (by norm_num : ¬ Nat.Prime 5515776) hp

private theorem k329eu_injective_quotient {L : Type*} [Group L] (X' : Subgroup L)
    (hbot : X' ⊓ Subgroup.center L = ⊥) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center L)).comp X'.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hx
    have hmem : (x : L) ∈ X' ⊓ Subgroup.center L := by
      refine ⟨x.2, ?_⟩
      exact (QuotientGroup.eq_one_iff (x : L)).mp (by simpa using hx)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  · intro hx
    rw [hx]
    simp

private theorem k329eu_decomp {L : Type*} [Group L] (X' : Subgroup L)
    (hbij : Function.Bijective ((QuotientGroup.mk' (Subgroup.center L)).comp X'.subtype)) :
    ∀ k : L, ∃ x ∈ X', ∃ z ∈ Subgroup.center L, x * z = k := by
  intro k
  rcases hbij.2 k with ⟨x, hx⟩
  have hx' : (QuotientGroup.mk' (Subgroup.center L)) (X'.subtype x) = k := by
    simpa only [MonoidHom.comp_apply] using hx
  have hmem : (X'.subtype x)⁻¹ * k ∈ Subgroup.center L := by
    refine (QuotientGroup.eq_one_iff ((X'.subtype x)⁻¹ * k)).mp ?_
    change (QuotientGroup.mk' (Subgroup.center L)) ((X'.subtype x)⁻¹ * k) = 1
    rw [map_mul, map_inv, hx']
    simp
  exact ⟨X'.subtype x, x.2, (X'.subtype x)⁻¹ * k, hmem, by group⟩

private theorem k329eu_sup_center_eq_top {L : Type*} [Group L] (X' : Subgroup L)
    (hbij : Function.Bijective ((QuotientGroup.mk' (Subgroup.center L)).comp X'.subtype)) :
    X' ⊔ Subgroup.center L = ⊤ := by
  rw [eq_top_iff]
  intro k _
  obtain ⟨x, hx, z, hz, hxz⟩ := k329eu_decomp X' hbij k
  rw [← hxz]
  exact Subgroup.mul_mem_sup hx hz

private theorem k329eu_commutator_le_of_decomp {L : Type*} [Group L] (X' : Subgroup L)
    (hdec : ∀ k : L, ∃ x ∈ X', ∃ z ∈ Subgroup.center L, x * z = k) :
    ⁅(⊤ : Subgroup L), ⊤⁆ ≤ X' := by
  rw [Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨x, hx, z, hz, rfl⟩ := hdec a
  obtain ⟨y, hy, w, hw, rfl⟩ := hdec b
  have hmul_left : ∀ c : L, ⁅x * z, c⁆ = ⁅x, c⁆ := by
    intro c
    have hz1 : ⁅z, c⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hz c).symm
    rw [commutatorElement_mul_left_eq_conj_mul, hz1]
    group
  have hmul_right : ⁅x, y * w⁆ = ⁅x, y⁆ := by
    have hw1 : ⁅x, w⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.mp hw x
    rw [commutatorElement_mul_right_eq_mul_conj, hw1]
    group
  rw [(hmul_left (y * w)).trans hmul_right, commutatorElement_def]
  exact X'.mul_mem (X'.mul_mem (X'.mul_mem hx hy) (X'.inv_mem hx)) (X'.inv_mem hy)

theorem k329_eq_of_psu38 :
    ∀ (G : Type) [Group G] [Finite G],
      CFSG.Open.IsQuasisimple ↥(CFSG.Open.genFittingFStar G) →
      ∀ X : Subgroup G, X ≤ CFSG.Open.genFittingFStar G → LieModel ↥X .PSU 3 2 3 →
        LieModel (↥(CFSG.Open.genFittingFStar G) ⧸
          Subgroup.center ↥(CFSG.Open.genFittingFStar G)) .PSU 3 2 3 →
        X = CFSG.Open.genFittingFStar G := by
  intro G _ _ hQ X hXK hX hS
  set K : Subgroup G := CFSG.Open.genFittingFStar G
  have hscX : CFSG.Open.StatedClassicalModel ↥X .PSU 3 2 3 := hX.statedClassicalModel (by decide)
  have hcardX : Nat.card ↥X = 5515776 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight hscX
  have hsimpleX : IsSimpleGroup ↥X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hX
  have hscS : CFSG.Open.StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSU 3 2 3 :=
    hS.statedClassicalModel (by decide)
  have hcardS : Nat.card (↥K ⧸ Subgroup.center ↥K) = 5515776 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight hscS
  have hsimpleX' : IsSimpleGroup ↥(X.subgroupOf K) := k329eu_simple_subgroupOf hXK hsimpleX
  have hcardX' : Nat.card ↥(X.subgroupOf K) = 5515776 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv, hcardX]
  have hbot : X.subgroupOf K ⊓ Subgroup.center ↥K = ⊥ :=
    k329eu_inf_center_eq_bot (X.subgroupOf K) hcardX' hsimpleX'
  have hinj : Function.Injective
      ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (X.subgroupOf K).subtype) :=
    k329eu_injective_quotient (X.subgroupOf K) hbot
  have : Finite (↥K ⧸ Subgroup.center ↥K) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center ↥K))
      (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
  have hbij : Function.Bijective
      ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (X.subgroupOf K).subtype) :=
    hinj.bijective_of_nat_card_le (by rw [hcardS, hcardX'])
  have hdec := k329eu_decomp (X.subgroupOf K) hbij
  have hsup : X.subgroupOf K ⊔ Subgroup.center ↥K = ⊤ :=
    k329eu_sup_center_eq_top (X.subgroupOf K) hbij
  have hcomm : ⁅(⊤ : Subgroup ↥K), ⊤⁆ ≤ X.subgroupOf K :=
    k329eu_commutator_le_of_decomp (X.subgroupOf K) hdec
  have hperfect : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = (⊤ : Subgroup ↥K) := by
    rw [← _root_.commutator_def]
    exact hQ.1
  have htop : X.subgroupOf K = ⊤ := top_le_iff.mp (hperfect ▸ hcomm)
  have hKX : K ≤ X := Subgroup.subgroupOf_eq_top.mp htop
  exact le_antisymm hXK hKX

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
