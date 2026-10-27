module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsIdx

public section

namespace CFSG.Quasithin.A312M23

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open CFSG.Quasithin.A312Words
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem comm_le_of_gen {Y N : Subgroup Γ} {ol : List Γ} {t : Γ} (h : IdxTwoData Y ol t)
    (hNY : N ≤ Y) (hol : ∀ g ∈ ol, g ∈ N) (hn : ∀ y ∈ Y, ∀ w ∈ N, y⁻¹ * w * y ∈ N) :
    ⁅Y, Y⁆ ≤ N ∧ Nat.card Y ≤ 2 * Nat.card N ∧ (t ∉ N → Nat.card Y = 2 * Nat.card N) := by
  classical
  have hnorm : (N.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNY]
    intro w y hw hy
    simpa using hn y⁻¹ (Y.inv_mem hy) w hw
  set Nn : Subgroup ↥Y := N.subgroupOf Y with hNn
  let φ : ↥Y →* ↥Y ⧸ Nn := QuotientGroup.mk' Nn
  let t' : ↥Y := ⟨t, h.tmem⟩
  have ht'sq : t' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using h.tsq)
  have hgen : ∀ g ∈ Subgroup.closure {x | x ∈ ol ++ [t]},
      ∃ hg : g ∈ Y, φ ⟨g, hg⟩ ∈ Subgroup.zpowers (φ t') := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      have hx' : x ∈ ol ∨ x = t := by simpa using hx
      rcases hx' with hx' | rfl
      · refine ⟨h.mem x hx', ?_⟩
        have : φ ⟨x, h.mem x hx'⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (hol x hx')
        rw [this]; exact Subgroup.one_mem _
      · exact ⟨h.tmem, Subgroup.mem_zpowers _⟩
    | one =>
      refine ⟨Y.one_mem, ?_⟩
      have : (⟨1, Y.one_mem⟩ : ↥Y) = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    | mul x y _ _ ihx ihy =>
      obtain ⟨hx, hxz⟩ := ihx
      obtain ⟨hy, hyz⟩ := ihy
      exact ⟨Y.mul_mem hx hy, by
        have : (⟨x * y, Y.mul_mem hx hy⟩ : ↥Y) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
        rw [this, map_mul]; exact Subgroup.mul_mem _ hxz hyz⟩
    | inv x _ ihx =>
      obtain ⟨hx, hxz⟩ := ihx
      exact ⟨Y.inv_mem hx, by
        have : (⟨x⁻¹, Y.inv_mem hx⟩ : ↥Y) = (⟨x, hx⟩ : ↥Y)⁻¹ := rfl
        rw [this, map_inv]; exact Subgroup.inv_mem _ hxz⟩
  have hall : ∀ y : ↥Y, φ y ∈ Subgroup.zpowers (φ t') := fun y => by
    obtain ⟨hy, hyz⟩ := hgen y.1 (h.gen y.2)
    exact hyz
  have hord : orderOf (φ t') ≤ 2 :=
    orderOf_le_of_pow_eq_one (by norm_num) (by rw [← map_pow, ht'sq, map_one])
  have hcardQ : Nat.card (↥Y ⧸ Nn) ≤ 2 := by
    have hle : Nat.card (↥Y ⧸ Nn) ≤ Nat.card (Subgroup.zpowers (φ t')) := by
      refine Nat.card_le_card_of_injective
        (fun q => ⟨q, ?_⟩ : (↥Y ⧸ Nn) → Subgroup.zpowers (φ t')) ?_
      · obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
        exact hall y
      · intro q1 q2 hq
        exact congrArg Subtype.val hq
    rw [Nat.card_zpowers] at hle
    exact hle.trans hord
  have hN : Nat.card Nn = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv
  have h5 := Subgroup.card_eq_card_quotient_mul_card_subgroup Nn
  refine ⟨?_, ?_, fun ht => ?_⟩
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h1 := hall ⟨g₁, hg₁⟩
    have h2 := hall ⟨g₂, hg₂⟩
    have hc : Commute (φ ⟨g₁, hg₁⟩) (φ ⟨g₂, hg₂⟩) := by
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp h1
      obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp h2
      rw [← ha, ← hb]
      exact Commute.zpow_zpow_self _ _ _
    have h3 : φ ⁅(⟨g₁, hg₁⟩ : ↥Y), ⟨g₂, hg₂⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hc
    have h4 : ⁅(⟨g₁, hg₁⟩ : ↥Y), ⟨g₂, hg₂⟩⁆ ∈ Nn := (QuotientGroup.eq_one_iff _).mp h3
    exact h4
  · rw [h5, hN]
    exact Nat.mul_le_mul_right _ hcardQ
  · have hne : Nn ≠ ⊤ := fun htop => by
      have : t' ∈ Nn := by rw [htop]; exact Subgroup.mem_top _
      exact ht this
    have hidx : 2 ≤ Nat.card (↥Y ⧸ Nn) := by
      have h6 : Nn.index ≠ 1 := by rwa [Ne, Subgroup.index_eq_one]
      have h7 : 0 < Nn.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have h8 : Nat.card (↥Y ⧸ Nn) = Nn.index := (Subgroup.index_eq_card Nn).symm
      omega
    rw [h5, hN]
    have : Nat.card (↥Y ⧸ Nn) = 2 := le_antisymm hcardQ hidx
    rw [this]

theorem perfectCore_eq_closure {S B Y : Subgroup Γ} {ol : List Γ} {t : Γ} (hS : IsPGroup 2 S)
    (hB : B ∈ lFamily S) (hY : B ⊔ S = Y) (hid : IdxTwoData Y ol t)
    (hn : ∀ v ∈ Subgroup.closure {x | x ∈ ol}, t⁻¹ * v * t ∈ Subgroup.closure {x | x ∈ ol}) :
    perfectCore Y = Subgroup.closure {x | x ∈ ol} ∧ ⁅Y, Y⁆ ≤ Subgroup.closure {x | x ∈ ol} ∧
      Nat.card Y ≤ 2 * Nat.card (Subgroup.closure {x | x ∈ ol}) ∧
      (t = 1 → Y = Subgroup.closure {x | x ∈ ol}) ∧
      (t ∉ Subgroup.closure {x | x ∈ ol} →
        Nat.card Y = 2 * Nat.card (Subgroup.closure {x | x ∈ ol})) := by
  set N : Subgroup Γ := Subgroup.closure {x | x ∈ ol} with hN
  have hNY : N ≤ Y := (Subgroup.closure_le Y).mpr fun g hg => hid.mem g hg
  have hnorm : ∀ g ∈ ol ++ [t], ∀ v ∈ N, g⁻¹ * v * g ∈ N := by
    intro g hg v hv
    rcases List.mem_append.mp hg with hg | hg
    · have hgN : g ∈ N := Subgroup.subset_closure hg
      exact N.mul_mem (N.mul_mem (N.inv_mem hgN) hv) hgN
    · have : g = t := by simpa using hg
      rw [this]
      exact hn v hv
  have hconj := idxTwo_conj_mem hid hnorm
  obtain ⟨hcomm, hcard, hcard2⟩ := comm_le_of_gen hid hNY (fun g hg => Subgroup.subset_closure hg)
    hconj
  have hol : ∀ g ∈ ol, g ∈ perfectCore Y := (perfectCore_quotient hS hB hY hid).1
  have hAN : perfectCore Y = N := by
    refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun g hg => hol g hg)
    calc perfectCore Y = ⁅perfectCore Y, perfectCore Y⁆ := (perfectCore_perfect Y).symm
      _ ≤ ⁅Y, Y⁆ := Subgroup.commutator_mono (perfectCore_le Y) (perfectCore_le Y)
      _ ≤ N := hcomm
  refine ⟨hAN, hcomm, hcard, fun ht => ?_, hcard2⟩
  refine le_antisymm (hid.gen.trans ((Subgroup.closure_le N).mpr fun g hg => ?_)) hNY
  rcases List.mem_append.mp hg with hg | hg
  · exact Subgroup.subset_closure hg
  · have : g = t := by simpa using hg
    rw [this, ht]
    exact N.one_mem

end CFSG.Quasithin.A312M23
