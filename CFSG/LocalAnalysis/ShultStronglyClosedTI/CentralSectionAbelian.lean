module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSectionBasic
public import Mathlib.GroupTheory.Index

import Mathlib.Tactic.Group
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.ShultStronglyClosedTI.CentralSection

open Subgroup

variable {P : Type*} [Group P]

@[expose] def twistHom {Q : Subgroup P} [Q.Normal] (hV : ∀ u v : P ⧸ Q, u * v = v * u)
    (σ : P →* P) : P →* P ⧸ Q :=
  MonoidHom.mk' (fun a => ((a⁻¹ * σ a : P) : P ⧸ Q)) fun a b => by
    have key : ∀ u v u' v' : P ⧸ Q, v⁻¹ * u⁻¹ * (u' * v') = u⁻¹ * u' * (v⁻¹ * v') := by
      intro u v u' v'
      calc v⁻¹ * u⁻¹ * (u' * v') = v⁻¹ * (u⁻¹ * u') * v' := by group
        _ = u⁻¹ * u' * v⁻¹ * v' := by rw [hV v⁻¹ (u⁻¹ * u')]
        _ = u⁻¹ * u' * (v⁻¹ * v') := by group
    simpa only [map_mul, mul_inv_rev, QuotientGroup.mk_mul, QuotientGroup.mk_inv] using
      key a b (σ a) (σ b)

theorem twistHom_apply {Q : Subgroup P} [Q.Normal] (hV : ∀ u v : P ⧸ Q, u * v = v * u)
    (σ : P →* P) (a : P) : twistHom hV σ a = ((a⁻¹ * σ a : P) : P ⧸ Q) :=
  rfl

namespace SingerSection

variable {X : Type*} [Group X] {Q T : Subgroup P} {φ : X →* MulAut P}

theorem quotient_comm [Q.Normal] (h : SingerSection Q T φ) (u v : P ⧸ Q) : u * v = v * u := by
  induction u using QuotientGroup.induction_on with | H a => ?_
  induction v using QuotientGroup.induction_on with | H b => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  convert h.commutator_mem b⁻¹ a⁻¹ using 1
  group

@[expose] def twist [Q.Normal] (h : SingerSection Q T φ) (x₁ : X) : P →* P ⧸ Q :=
  twistHom h.quotient_comm (φ x₁).toMonoidHom

@[expose] def twistSubgroup [Q.Normal] (h : SingerSection Q T φ) (x₁ : X) : Subgroup P :=
  (h.twist x₁).range.comap (QuotientGroup.mk' Q)

theorem twist_eq_one_iff [Q.Normal] (h : SingerSection Q T φ) (x₁ : X) {a : P} :
    h.twist x₁ a = 1 ↔ a⁻¹ * φ x₁ a ∈ Q :=
  QuotientGroup.eq_one_iff _

theorem mem_twistSubgroup_iff [Q.Normal] (h : SingerSection Q T φ) (x₁ : X) {g : P} :
    g ∈ h.twistSubgroup x₁ ↔ ∃ a : P, (a⁻¹ * φ x₁ a)⁻¹ * g ∈ Q := by
  simp only [twistSubgroup, mem_comap, MonoidHom.mem_range, QuotientGroup.mk'_apply]
  exact exists_congr fun a => QuotientGroup.eq

theorem le_twistSubgroup_self [Q.Normal] (h : SingerSection Q T φ) (x₁ : X) :
    Q ≤ h.twistSubgroup x₁ := fun z hz =>
  (h.mem_twistSubgroup_iff x₁).mpr ⟨1, by simpa using hz⟩

theorem mem_sup_of_κ_eq_one (h : SingerSection Q T φ) {t₀ : P} (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1)
    {x₁ : X} (hx₁ : x₁ ≠ 1) {a : P} (ha : h.κ t₀ (a⁻¹ * φ x₁ a) = 1) : a ∈ Q ⊔ T := by
  rw [← h.κ_eq_one_iff ht₀ ht₀1]
  rw [map_mul, map_inv, ← h.map_κ ht₀, inv_mul_eq_one] at ha
  by_contra hne
  exact hx₁ (h.eq_one_of_fixed x₁ _ (h.κ_mem t₀ a) hne ha.symm)

theorem ker_twist [Q.Normal] (h : SingerSection Q T φ) {t₀ : P} (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1)
    {x₁ : X} (hx₁ : x₁ ≠ 1) : (h.twist x₁).ker = Q ⊔ T := by
  apply le_antisymm
  · intro a ha
    rw [MonoidHom.mem_ker, h.twist_eq_one_iff] at ha
    exact h.mem_sup_of_κ_eq_one ht₀ ht₀1 hx₁ (h.κ_eq_one_of_mem t₀ ha)
  · refine sup_le (fun z hz => ?_) (fun t ht => ?_)
    · rw [MonoidHom.mem_ker, h.twist_eq_one_iff]
      exact mul_mem (inv_mem hz) (h.map_mem x₁ z hz)
    · rw [MonoidHom.mem_ker, h.twist_eq_one_iff, h.fixed x₁ t ht, inv_mul_cancel]
      exact one_mem Q

theorem mem_of_mem_twistSubgroup [Q.Normal] (h : SingerSection Q T φ) {t₀ : P} (ht₀ : t₀ ∈ T)
    (ht₀1 : t₀ ≠ 1) {x₁ : X} (hx₁ : x₁ ≠ 1) {g : P} (hg : g ∈ h.twistSubgroup x₁)
    (hκ : h.κ t₀ g = 1) : g ∈ Q := by
  obtain ⟨a, ha⟩ := (h.mem_twistSubgroup_iff x₁).mp hg
  have h1 : h.κ t₀ (a⁻¹ * φ x₁ a) = 1 := by
    have := h.κ_eq_one_of_mem t₀ ha
    rwa [map_mul, map_inv, hκ, mul_one, inv_eq_one] at this
  have h2 : a⁻¹ * φ x₁ a ∈ Q := by
    rw [← h.twist_eq_one_iff, ← MonoidHom.mem_ker, h.ker_twist ht₀ ht₀1 hx₁]
    exact h.mem_sup_of_κ_eq_one ht₀ ht₀1 hx₁ h1
  have hg' : g = a⁻¹ * φ x₁ a * ((a⁻¹ * φ x₁ a)⁻¹ * g) := by group
  rw [hg']
  exact mul_mem h2 ha

theorem map_mem_twistSubgroup [Q.Normal] (h : SingerSection Q T φ) (x₁ x : X) {g : P}
    (hg : g ∈ h.twistSubgroup x₁) : φ x g ∈ h.twistSubgroup x₁ := by
  obtain ⟨a, ha⟩ := (h.mem_twistSubgroup_iff x₁).mp hg
  refine (h.mem_twistSubgroup_iff x₁).mpr ⟨φ x a, ?_⟩
  have := h.map_mem x _ ha
  simp only [map_mul, map_inv] at this
  rwa [h.map_comm x x₁] at this

theorem t₀_notMem_twistSubgroup [Q.Normal] (h : SingerSection Q T φ) {t₀ : P} (ht₀ : t₀ ∈ T)
    (ht₀1 : t₀ ≠ 1) {x₁ : X} (hx₁ : x₁ ≠ 1) : t₀ ∉ h.twistSubgroup x₁ := by
  intro ht
  have hκ : h.κ t₀ t₀ = 1 := by
    rw [h.κ_apply]
    group
  have hmem : t₀ ∈ Q ⊓ T := ⟨h.mem_of_mem_twistSubgroup ht₀ ht₀1 hx₁ ht hκ, ht₀⟩
  rw [h.inf_eq_bot, mem_bot] at hmem
  exact ht₀1 hmem

theorem exists_inv_map_mul_mem [Q.Normal] (h : SingerSection Q T φ) {t₀ : P} (ht₀ : t₀ ∈ T)
    (ht₀1 : t₀ ≠ 1) {x₁ : X} (hx₁ : x₁ ≠ 1) {r₀ g : P} (hr₀ : r₀ ∈ h.twistSubgroup x₁)
    (hr₀Q : r₀ ∉ Q) (hg : g ∈ h.twistSubgroup x₁) (hgQ : g ∉ Q) :
    ∃ x : X, (φ x r₀)⁻¹ * g ∈ Q := by
  have hκr₀ : h.κ t₀ r₀ ≠ 1 := fun h1 => hr₀Q (h.mem_of_mem_twistSubgroup ht₀ ht₀1 hx₁ hr₀ h1)
  have hκg : h.κ t₀ g ≠ 1 := fun h1 => hgQ (h.mem_of_mem_twistSubgroup ht₀ ht₀1 hx₁ hg h1)
  obtain ⟨x, hx⟩ := h.exists_map_eq _ (h.κ_mem t₀ r₀) hκr₀ _ (h.κ_mem t₀ g) hκg
  refine ⟨x, h.mem_of_mem_twistSubgroup ht₀ ht₀1 hx₁
    (mul_mem (inv_mem (h.map_mem_twistSubgroup x₁ x hr₀)) hg) ?_⟩
  rw [map_mul, map_inv, ← h.map_κ ht₀, hx, inv_mul_cancel]

theorem sq_mul_eq_of_mem_twistSubgroup [Q.Normal] (h : SingerSection Q T φ) {t₀ : P}
    (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1) {x₁ : X} (hx₁ : x₁ ≠ 1)
    (hR : ∃ r ∈ h.twistSubgroup x₁, r ∉ Q) {g₁ g₂ : P} (hg₁ : g₁ ∈ h.twistSubgroup x₁)
    (hg₂ : g₂ ∈ h.twistSubgroup x₁) : (g₁ * g₂) ^ 2 = g₁ ^ 2 * g₂ ^ 2 := by
  obtain ⟨r₀, hr₀, hr₀Q⟩ := hR
  have horbit : ∀ g ∈ h.twistSubgroup x₁, g ∉ Q →
      ∃ x : X, g ^ 2 = φ x (r₀ ^ 2) ∧ h.κ t₀ g = φ x (h.κ t₀ r₀) := by
    intro g hg hgQ
    obtain ⟨x, hx⟩ := h.exists_inv_map_mul_mem ht₀ ht₀1 hx₁ hr₀ hr₀Q hg hgQ
    have hg' : g = φ x r₀ * ((φ x r₀)⁻¹ * g) := by group
    refine ⟨x, ?_, ?_⟩
    · rw [hg', h.sq_mul_of_mem _ hx, map_pow]
    · rw [hg', map_mul, h.κ_eq_one_of_mem t₀ hx, mul_one, h.map_κ ht₀]
  by_cases hr₀2 : r₀ ^ 2 = 1
  · have hsq : ∀ g ∈ h.twistSubgroup x₁, g ^ 2 = 1 := by
      intro g hg
      by_cases hgQ : g ∈ Q
      · exact h.sq_eq_one g hgQ
      · obtain ⟨x, hx, -⟩ := horbit g hg hgQ
        rw [hx, hr₀2, map_one]
    rw [hsq _ (mul_mem hg₁ hg₂), hsq g₁ hg₁, hsq g₂ hg₂, one_mul]
  · have hκr₀ : h.κ t₀ r₀ ≠ 1 := fun h1 => hr₀Q (h.mem_of_mem_twistSubgroup ht₀ ht₀1 hx₁ hr₀ h1)
    obtain ⟨y, hy⟩ := h.exists_map_eq _ (h.κ_mem t₀ r₀) hκr₀ _ (h.sq_mem r₀) hr₀2
    have hsq : ∀ g ∈ h.twistSubgroup x₁, g ^ 2 = φ y (h.κ t₀ g) := by
      intro g hg
      by_cases hgQ : g ∈ Q
      · rw [h.sq_eq_one g hgQ, h.κ_eq_one_of_mem t₀ hgQ, map_one]
      · obtain ⟨x, hx, hxκ⟩ := horbit g hg hgQ
        rw [hx, hxκ, ← hy, h.map_comm]
    rw [hsq _ (mul_mem hg₁ hg₂), hsq g₁ hg₁, hsq g₂ hg₂, map_mul, map_mul]

theorem mul_comm_of_mem_twistSubgroup [Q.Normal] (h : SingerSection Q T φ) {t₀ : P}
    (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1) {x₁ : X} (hx₁ : x₁ ≠ 1)
    (hR : ∃ r ∈ h.twistSubgroup x₁, r ∉ Q) {g₁ g₂ : P} (hg₁ : g₁ ∈ h.twistSubgroup x₁)
    (hg₂ : g₂ ∈ h.twistSubgroup x₁) : g₁ * g₂ = g₂ * g₁ := by
  have key := h.mul_sq g₁ g₂
  rw [h.sq_mul_eq_of_mem_twistSubgroup ht₀ ht₀1 hx₁ hR hg₁ hg₂, mul_assoc _ (g₁ ^ 2), eq_comm,
    mul_eq_right, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at key
  exact key.symm

theorem card_twistSubgroup [Finite P] [Q.Normal] (h : SingerSection Q T φ) {t₀ : P}
    (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1) {x₁ : X} (hx₁ : x₁ ≠ 1)
    (hP : Nat.card P = 2 * Nat.card Q ^ 2) (hH : Nat.card (Q ⊔ T : Subgroup P) = 2 * Nat.card Q) :
    Nat.card (h.twistSubgroup x₁) = Nat.card Q ^ 2 := by
  have hq : 0 < Nat.card Q := Nat.card_pos
  have h1 := card_mul_index (h.twistSubgroup x₁)
  have h2 : (h.twistSubgroup x₁).index = (h.twist x₁).range.index :=
    index_comap_of_surjective _ (QuotientGroup.mk'_surjective Q)
  have h3 := card_mul_index (h.twist x₁).range
  have h5 := card_mul_index Q
  have h6 : Nat.card (h.twist x₁).range = (Q ⊔ T).index := by
    rw [← index_ker, h.ker_twist ht₀ ht₀1 hx₁]
  have h7 := card_mul_index (Q ⊔ T)
  rw [hH, hP] at h7
  rw [hP] at h5 h1
  have hidxH : (Q ⊔ T).index = Nat.card Q :=
    Nat.eq_of_mul_eq_mul_left (show 0 < 2 * Nat.card Q by omega) (by rw [h7]; ring)
  have hidxQ : Q.index = 2 * Nat.card Q :=
    Nat.eq_of_mul_eq_mul_left hq (by rw [h5]; ring)
  rw [h6, hidxH, ← index_eq_card, hidxQ] at h3
  have hidxR : (h.twist x₁).range.index = 2 :=
    Nat.eq_of_mul_eq_mul_left hq (h3.trans (mul_comm 2 _))
  rw [h2, hidxR] at h1
  omega

theorem le_twistSubgroup [Finite P] [Q.Normal] (h : SingerSection Q T φ) {t₀ : P}
    (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1) {x₁ : X} (hx₁ : x₁ ≠ 1) (hq : 4 ≤ Nat.card Q)
    (hP : Nat.card P = 2 * Nat.card Q ^ 2) (hR : Nat.card (h.twistSubgroup x₁) = Nat.card Q ^ 2)
    (hRcomm : ∀ a ∈ h.twistSubgroup x₁, ∀ b ∈ h.twistSubgroup x₁, a * b = b * a)
    {S : Subgroup P} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hScard : Nat.card S = Nat.card Q ^ 2) :
    S ≤ h.twistSubgroup x₁ := by
  intro g hg
  by_contra hgR
  have hidx : (h.twistSubgroup x₁).index = 2 := by
    have := card_mul_index (h.twistSubgroup x₁)
    rw [hR, hP] at this
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (this.trans (mul_comm _ _))
  have hr₁ : g * t₀ ∈ h.twistSubgroup x₁ :=
    (mul_mem_iff_of_index_two hidx).mpr (iff_of_false hgR (h.t₀_notMem_twistSubgroup ht₀ ht₀1 hx₁))
  have hinf : h.twistSubgroup x₁ ⊓ S ≤ Q := by
    rintro s ⟨hsR, hsS⟩
    refine h.mem_of_mem_twistSubgroup ht₀ ht₀1 hx₁ hsR ?_
    rw [h.κ_eq_one_iff ht₀ ht₀1, ← h.centralizer_eq t₀ ht₀ ht₀1, mem_centralizer_singleton_iff]
    have h1 : s * (g * t₀) = g * t₀ * s := hRcomm s hsR _ hr₁
    rw [← mul_assoc, hS s hsS g hg, mul_assoc, mul_assoc] at h1
    exact mul_left_cancel h1
  have hrel : (h.twistSubgroup x₁).relIndex S ≤ 2 := by
    calc (h.twistSubgroup x₁).relIndex S ≤ (h.twistSubgroup x₁).relIndex ⊤ :=
          relIndex_le_of_le_right le_top (by rw [relIndex_top_right, hidx]; norm_num)
      _ = 2 := by rw [relIndex_top_right, hidx]
  have hcardinf : Nat.card (h.twistSubgroup x₁ ⊓ S : Subgroup P) ≤ Nat.card Q := card_le_of_le hinf
  have hmul := relIndex_mul_card (h.twistSubgroup x₁) S
  rw [hScard] at hmul
  nlinarith [Nat.mul_le_mul hrel hcardinf]

end SingerSection

end CFSG.ShultStronglyClosedTI.CentralSection
