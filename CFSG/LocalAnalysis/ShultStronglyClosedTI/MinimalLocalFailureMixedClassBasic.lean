module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedPointModelHull

public section

namespace CFSG.ShultStronglyClosedTI.MixedClass

open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem mem_pointClass_iff_isConj {z t : G} : t ∈ involutionPointClass z ↔ IsConj z t := by
  rw [pointClass_eq_conjAct_orbit, ConjAct.mem_orbit_conjAct, isConj_comm]

theorem two_transitive_of_conj {N : Subgroup G} {Δ : Set G} {u : G}
    (hpres : ∀ n ∈ N, ∀ x ∈ Δ, n * x * n⁻¹ ∈ Δ)
    (htrans : ∀ x ∈ Δ, ∃ n ∈ N, n⁻¹ * u * n = x)
    (hstab : ∀ x ∈ Δ, ∀ y ∈ Δ, x ≠ u → y ≠ u →
      ∃ n ∈ N, n⁻¹ * u * n = u ∧ n⁻¹ * x * n = y) :
    ∀ a ∈ Δ, ∀ b ∈ Δ, ∀ c ∈ Δ, ∀ d ∈ Δ, a ≠ b → c ≠ d →
      ∃ n ∈ N, n⁻¹ * a * n = c ∧ n⁻¹ * b * n = d := by
  intro a ha b hb c hc d hd hab hcd
  obtain ⟨n₁, hn₁, h₁⟩ := htrans a ha
  obtain ⟨n₂, hn₂, h₂⟩ := htrans c hc
  have hb'u : n₁ * b * n₁⁻¹ ≠ u := by
    intro heq
    apply hab
    rw [← h₁, ← heq]
    group
  have hd'u : n₂ * d * n₂⁻¹ ≠ u := by
    intro heq
    apply hcd
    rw [← h₂, ← heq]
    group
  obtain ⟨m, hm, hmu, hmb⟩ :=
    hstab _ (hpres n₁ hn₁ b hb) _ (hpres n₂ hn₂ d hd) hb'u hd'u
  refine ⟨n₁⁻¹ * m * n₂, N.mul_mem (N.mul_mem (N.inv_mem hn₁) hm) hn₂, ?_, ?_⟩
  · calc (n₁⁻¹ * m * n₂)⁻¹ * a * (n₁⁻¹ * m * n₂) =
          n₂⁻¹ * (m⁻¹ * (n₁ * a * n₁⁻¹) * m) * n₂ := by group
      _ = n₂⁻¹ * (m⁻¹ * u * m) * n₂ := by rw [← h₁]; group
      _ = c := by rw [hmu, h₂]
  · calc (n₁⁻¹ * m * n₂)⁻¹ * b * (n₁⁻¹ * m * n₂) =
          n₂⁻¹ * (m⁻¹ * (n₁ * b * n₁⁻¹) * m) * n₂ := by group
      _ = d := by rw [hmb]; group

theorem mem_normalizer_of_conj_mem {Δ : Set G} {c : G}
    (h₁ : ∀ x ∈ Δ, c⁻¹ * x * c ∈ Δ) (h₂ : ∀ x ∈ Δ, c * x * c⁻¹ ∈ Δ) :
    c ∈ Subgroup.normalizer Δ := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  refine ⟨h₂ x, fun hx => ?_⟩
  have hmem := h₁ _ hx
  rwa [show c⁻¹ * (c * x * c⁻¹) * c = x by group] at hmem

theorem conj_mem_of_mem_normalizer {Δ : Set G} {c : G} (hc : c ∈ Subgroup.normalizer Δ)
    {x : G} (hx : x ∈ Δ) : c * x * c⁻¹ ∈ Δ :=
  (Subgroup.mem_set_normalizer_iff.mp hc x).mp hx

theorem card_subgroupOf_eq (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup G) := by
  rw [← Subgroup.inf_subgroupOf_right]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

theorem card_rightCosetSpace (H : Subgroup G) : Nat.card (rightCosetSpace H) = H.index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)

theorem card_base_orbit_mul (H Y : Subgroup G) :
    Nat.card {omega : rightCosetSpace H |
        ∃ y ∈ Y, rightCosetTranslate H (rightCosetMk H 1) y = omega} *
      Nat.card (H ⊓ Y : Subgroup G) = Nat.card Y := by
  obtain ⟨ι, hinj, hrange, -, -⟩ := FixedPointModel.orbit_coset_embedding H Y
  rw [← hrange, Nat.card_range_of_injective hinj, ← card_subgroupOf_eq, mul_comm,
    ← Subgroup.index_eq_card]
  exact Subgroup.card_mul_index _

theorem card_centralizer_mul_card_conjugacyWithin {H : Subgroup G} {z : G}
    (hle : Subgroup.centralizer ({z} : Set G) ≤ H) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) * Nat.card (conjugacyWithin H z) =
      Nat.card H := by
  rw [conjugacyWithin_card_eq_centralizer_index,
    ← Subgroup.card_mul_index ((Subgroup.centralizer ({z} : Set G)).subgroupOf H),
    card_subgroupOf_eq, inf_eq_left.mpr hle]

theorem eq_one_of_fixes_all (hsimple : IsSimpleGroup G) {H : Subgroup G} (hH : H ≠ ⊤) {u : G}
    (hall : ∀ omega : rightCosetSpace H, rightCosetTranslate H omega u = omega) : u = 1 := by
  have hconj : ∀ g : G, g * u * g⁻¹ ∈ H := fun g =>
    (translate_mk_fixed_iff H g u).mp (hall (rightCosetMk H g))
  have hle : Subgroup.normalClosure ({u} : Set G) ≤ H := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨c, rfl⟩ := isConj_iff.mp hax
    exact hconj c
  have humem : u ∈ Subgroup.normalClosure ({u} : Set G) :=
    Subgroup.subset_normalClosure (Set.mem_singleton u)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (self := hsimple)
    (Subgroup.normalClosure ({u} : Set G)) with hbot | htop
  · rwa [hbot, Subgroup.mem_bot] at humem
  · exact absurd (top_unique (htop ▸ hle)) hH

theorem conj_mem_coset {Q : Subgroup G} (hQ : CFSG.Open.IsElemAbelian 2 Q) {u : G}
    (huu : u * u = 1) (huQ : ∀ v ∈ Q, u⁻¹ * v * u ∈ Q) {q : G} (hq : q ∈ Q) :
    q⁻¹ * u * q ∈ (fun e => u * e) ''
      ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQ.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ a ∈ Q, a * a = 1 := fun a ha => by rw [← sq]; exact hQ.2 a ha
  have hq' : u⁻¹ * q⁻¹ * u ∈ Q := huQ _ (Q.inv_mem hq)
  have heQ : u⁻¹ * q⁻¹ * u * q ∈ Q := Q.mul_mem hq' hq
  refine ⟨u⁻¹ * q⁻¹ * u * q, ⟨heQ, ?_⟩, by group⟩
  change u⁻¹ * q⁻¹ * u * q ∈ Subgroup.centralizer ({u} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hqinv : q⁻¹ = q := inv_eq_of_mul_eq_one_right (hsq q hq)
  have ha : u * q * u ∈ Q := by
    have := hq'
    rwa [huinv, hqinv] at this
  calc u⁻¹ * q⁻¹ * u * q * u = (u * q * u) * q * u := by rw [huinv, hqinv]
    _ = q * (u * q * u) * u := by rw [hcomm _ ha q hq]
    _ = q * u * q * (u * u) := by group
    _ = u * (u⁻¹ * q⁻¹ * u * q) := by rw [huu, hqinv]; group

variable [Finite G]

theorem coset_eq_conjugacyWithin {Q : Subgroup G} (hQ : CFSG.Open.IsElemAbelian 2 Q) {u : G}
    (huu : u * u = 1) (huQ : ∀ v ∈ Q, u⁻¹ * v * u ∈ Q)
    (hsq : Nat.card Q = Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ^ 2) :
    (fun e => u * e) '' ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) =
      conjugacyWithin Q u := by
  set E := (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G)
  have hsub : conjugacyWithin Q u ⊆ (fun e => u * e) '' (E : Set G) := by
    rintro x ⟨q, rfl⟩
    exact conj_mem_coset hQ huu huQ q.2
  have hE0 : 0 < Nat.card E := Nat.card_pos
  have hindex : ((Subgroup.centralizer ({u} : Set G)).subgroupOf Q).index = Nat.card E := by
    have hmul := Subgroup.card_mul_index ((Subgroup.centralizer ({u} : Set G)).subgroupOf Q)
    rw [card_subgroupOf_eq, inf_comm, hsq, sq] at hmul
    exact Nat.eq_of_mul_eq_mul_left hE0 hmul
  have hcard : Nat.card ((fun e => u * e) '' (E : Set G)) = Nat.card (conjugacyWithin Q u) := by
    rw [Nat.card_image_of_injective (mul_right_injective u),
      conjugacyWithin_card_eq_centralizer_index,
      hindex]
    rfl
  symm
  apply Set.eq_of_subset_of_ncard_le hsub
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard]

end CFSG.ShultStronglyClosedTI.MixedClass
