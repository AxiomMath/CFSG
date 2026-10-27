module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.ASimple
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Basic

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral

open CFSG.SignalizerFunctorTheorem.Nonsolvable

structure Setup (p : ℕ) {Γ : Type u} [Group Γ] (A W Z : Subgroup Γ) (T : Γ → Subgroup Γ) :
    Prop where
  prime : p.Prime
  isElemAbelian : IsElemAbelian p A
  rank : p ^ 3 ≤ Nat.card A
  normalizes : A ≤ Subgroup.normalizer (W : Set Γ)
  coprime : Nat.Coprime p (Nat.card W)
  perfect : ⁅W, W⁆ = W
  le : Z ≤ W
  central : ∀ z ∈ Z, ∀ w ∈ W, z * w = w * z
  ne_bot : Z ≠ ⊥
  normalizes_Z : A ≤ Subgroup.normalizer (Z : Set Γ)
  inf_eq_bot : A ⊓ Z = ⊥
  minimal : ∀ Z' : Subgroup Γ, Z' ≤ Z → A ≤ Subgroup.normalizer (Z' : Set Γ) → Z' = ⊥ ∨ Z' = Z
  fixed : ∀ b ∈ A, b ≠ 1 → T b ≤ W ∧ T b ⊓ Z = ⊥ ∧
    ∀ w ∈ W ⊓ Subgroup.centralizer {b}, ∃ z ∈ Z, ∃ t ∈ T b, w = z * t
  meet : ∀ M : Subgroup Γ, M ≤ W → (M.subgroupOf W).Normal →
    A ≤ Subgroup.normalizer (M : Set Γ) → M ≠ W → ∀ b ∈ A, b ≠ 1 → T b ⊓ M = ⊥

variable {Γ : Type u} [Group Γ] {p : ℕ} {A W Z : Subgroup Γ} {T : Γ → Subgroup Γ}

namespace Setup

theorem comm (h : Setup p A W Z T) {a b : Γ} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  comm_of_mem_of_isMulCommutative h.isElemAbelian.1 ha hb

theorem conj_mem_W (h : Setup p A W Z T) {a x : Γ} (ha : a ∈ A) (hx : x ∈ W) : a * x * a⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.mp (h.normalizes ha) x).mp hx

theorem conj_mem_Z (h : Setup p A W Z T) {a x : Γ} (ha : a ∈ A) (hx : x ∈ Z) : a * x * a⁻¹ ∈ Z :=
  (Subgroup.mem_normalizer_iff.mp (h.normalizes_Z ha) x).mp hx

theorem pow_eq_one (h : Setup p A W Z T) {a : Γ} (ha : a ∈ A) : a ^ p = 1 :=
  h.isElemAbelian.2 a ha

theorem sq_le_card (h : Setup p A W Z T) : p ^ 2 ≤ Nat.card A :=
  le_trans (Nat.pow_le_pow_right h.prime.pos (by norm_num)) h.rank

theorem eq_of_normal [Finite Γ] (h : Setup p A W Z T) {M : Subgroup Γ} (hMW : M ≤ W)
    (hMn : (M.subgroupOf W).Normal) (hMA : A ≤ Subgroup.normalizer (M : Set Γ)) (hZM : Z ≤ M)
    (hMne : M ≠ W) : M = Z := by
  refine le_antisymm ?_ hZM
  have hcop : Nat.Coprime p (Nat.card M) :=
    h.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hMW)
  rw [← iSup_inf_centralizer h.prime h.isElemAbelian h.sq_le_card hMA hcop]
  refine iSup₂_le fun b hb => iSup_le fun hb1 c hc => ?_
  obtain ⟨hcM, hcb⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨-, -, hfix⟩ := h.fixed b hb hb1
  obtain ⟨z, hz, t, ht, rfl⟩ := hfix c (Subgroup.mem_inf.mpr ⟨hMW hcM, hcb⟩)
  have htM : t ∈ M := by
    have : t = z⁻¹ * (z * t) := by group
    rw [this]
    exact mul_mem (inv_mem (hZM hz)) hcM
  have htbot : t ∈ T b ⊓ M := ⟨ht, htM⟩
  rw [h.meet M hMW hMn hMA hMne b hb hb1, Subgroup.mem_bot] at htbot
  rw [htbot, mul_one]
  exact hz

variable [Z.Normal]

theorem exists_not_commute_map (h : Setup p A W Z T) :
    ∃ x ∈ W.map (QuotientGroup.mk' Z), ∃ y ∈ W.map (QuotientGroup.mk' Z), x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ g₁ ∈ W, ∀ g₂ ∈ W, ⁅g₁, g₂⁆ ∈ Z := by
    intro g₁ hg₁ g₂ hg₂
    have h1 : QuotientGroup.mk' Z ⁅g₁, g₂⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcon _ (Subgroup.mem_map_of_mem _ hg₁) _ (Subgroup.mem_map_of_mem _ hg₂)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hWZ : W ≤ Z := by
    calc W = ⁅W, W⁆ := h.perfect.symm
      _ ≤ Z := Subgroup.commutator_le.mpr hcomm
  have hbot : ⁅W, W⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (h.central x (hWZ hx) g hg).symm
  rw [h.perfect] at hbot
  exact h.ne_bot (eq_bot_iff.mpr (h.le.trans hbot.le))

theorem isASimple [Finite Γ] (h : Setup p A W Z T) :
    IsASimple (A.map (QuotientGroup.mk' Z)) (W.map (QuotientGroup.mk' Z)) := by
  refine ⟨?_, h.exists_not_commute_map, ?_⟩
  · refine le_normalizer_of_conj_mem ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨a * x * a⁻¹, h.conj_mem_W ha hx, by simp⟩
  · intro N hNle hNn hNA
    have hZM : Z ≤ W ⊓ N.comap (QuotientGroup.mk' Z) := fun z hz =>
      ⟨h.le hz, by
        show QuotientGroup.mk' Z z ∈ N
        rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz]
        exact one_mem N⟩
    have hMW : W ⊓ N.comap (QuotientGroup.mk' Z) ≤ W := inf_le_left
    have hMn : ((W ⊓ N.comap (QuotientGroup.mk' Z)).subgroupOf W).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hMW]
      intro m g hm hg
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg hm.1) (inv_mem hg), ?_⟩
      have := (Subgroup.normal_subgroupOf_iff hNle).mp hNn (QuotientGroup.mk' Z m)
        (QuotientGroup.mk' Z g) hm.2 (Subgroup.mem_map_of_mem _ hg)
      simpa using this
    have hMA : A ≤ Subgroup.normalizer ((W ⊓ N.comap (QuotientGroup.mk' Z) : Subgroup Γ) :
        Set Γ) := by
      refine le_normalizer_of_conj_mem fun a ha m hm => Subgroup.mem_inf.mpr
        ⟨h.conj_mem_W ha hm.1, ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp (hNA (Subgroup.mem_map_of_mem _ ha))
        (QuotientGroup.mk' Z m)).mp hm.2
      simpa using this
    by_cases hMeq : W ⊓ N.comap (QuotientGroup.mk' Z) = W
    · refine Or.inr (le_antisymm hNle ?_)
      rintro _ ⟨w, hw, rfl⟩
      have hwM : w ∈ W ⊓ N.comap (QuotientGroup.mk' Z) := by rw [hMeq]; exact hw
      exact hwM.2
    · refine Or.inl (eq_bot_iff.mpr fun n hn => ?_)
      obtain ⟨w, hw, rfl⟩ := hNle hn
      have hwM : w ∈ W ⊓ N.comap (QuotientGroup.mk' Z) := ⟨hw, hn⟩
      rw [h.eq_of_normal hMW hMn hMA hZM hMeq] at hwM
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hwM

end Setup

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral
