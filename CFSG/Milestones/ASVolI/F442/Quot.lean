module

public import CFSG.Milestones.ASVolI.F442.Perm
import Mathlib.Tactic.Group

public section

namespace CFSG.ASVolI

section Quot

variable {M : Type*} [Group M]

@[expose] def burnsideF42g_FixIn (H X : Subgroup M) (c : M) : Prop :=
  ∀ k ∈ H, k⁻¹ * c * k ∈ X → k ∈ X

theorem burnsideF42g_fixIn_of_mul {H X : Subgroup M} {t c : M} (htX : t ∈ X)
    (hcen : ∀ h ∈ H, h * t = t * h) (hf : burnsideF42g_FixIn H X (c * t)) :
    burnsideF42g_FixIn H X c := by
  intro k hk hkc
  apply hf k hk
  have e : k⁻¹ * (c * t) * k = k⁻¹ * c * k * t := by
    rw [show k⁻¹ * (c * t) * k = k⁻¹ * c * (t * k) by group, ← hcen k hk]
    group
  rw [e]
  exact X.mul_mem hkc htX

theorem burnsideF42g_mem_zpowers_iff {G : Type*} [Group G] {g y : G} (hg : g * g = 1) :
    y ∈ Subgroup.zpowers g ↔ y = 1 ∨ y = g := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, zpow_two, hg, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hg, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

variable [Finite M] {H X : Subgroup M} {t : M}

theorem burnsideF42g_quot_data (htH : t ∈ H) (htX : t ∈ X) (hcen : ∀ h ∈ H, h * t = t * h)
    (ht2 : t * t = 1) :
    ∃ hN : (Subgroup.zpowers (⟨t, htH⟩ : ↥H)).Normal,
      (∀ y : ↥H, (QuotientGroup.mk' (Subgroup.zpowers (⟨t, htH⟩ : ↥H)) y ∈
          (X.subgroupOf H).map (QuotientGroup.mk' (Subgroup.zpowers (⟨t, htH⟩ : ↥H)))) ↔
          (y : M) ∈ X) ∧
      (∀ y y' : ↥H, QuotientGroup.mk' (Subgroup.zpowers (⟨t, htH⟩ : ↥H)) y =
          QuotientGroup.mk' (Subgroup.zpowers (⟨t, htH⟩ : ↥H)) y' ↔
          (y' : M) = y ∨ (y' : M) = y * t) := by
  set t' : ↥H := ⟨t, htH⟩ with ht'
  have ht'2 : t' * t' = 1 := Subtype.ext ht2
  have hmemN : ∀ n : ↥H, n ∈ Subgroup.zpowers t' ↔ (n : M) = 1 ∨ (n : M) = t := by
    intro n
    rw [burnsideF42g_mem_zpowers_iff ht'2]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  have hN : (Subgroup.zpowers t').Normal := by
    refine ⟨fun n hn g => ?_⟩
    rcases (hmemN n).mp hn with h | h
    · have : n = 1 := Subtype.ext h
      rw [this, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · have : n = t' := Subtype.ext h
      rw [this]
      have hg : g * t' = t' * g := Subtype.ext (hcen g g.2)
      rw [hg, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers _
  refine ⟨hN, fun y => ?_, fun y y' => ?_⟩
  · constructor
    · rintro ⟨x, hx, hxy⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
      rcases (hmemN _).mp hxy with h | h
      · have : (y : M) = x := by
          have := congrArg (fun w => (x : M) * w) h
          simpa using this
        rw [this]
        exact hx
      · have : (y : M) = x * t := by
          have := congrArg (fun w => (x : M) * w) h
          simpa using this
        rw [this]
        exact X.mul_mem hx htX
    · intro hy
      exact ⟨y, hy, rfl⟩
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hmemN]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · rintro (h | h)
      · left
        have := congrArg (fun w => (y : M) * w) h
        simpa using this
      · right
        have := congrArg (fun w => (y : M) * w) h
        simpa using this
    · rintro (h | h)
      · left
        rw [h]
        group
      · right
        rw [h]
        group

theorem burnsideF42g_le_of_fix1_mod {a b : M} (htH : t ∈ H) (htX : t ∈ X) (hXH : X ≤ H)
    (hcen : ∀ h ∈ H, h * t = t * h) (ht2 : t * t = 1) (haX : a ∈ X) (hbX : b ∈ X)
    (ha : a * a = 1) (hb : b * b = 1) (hfa : burnsideF42g_FixIn H X a)
    (hfb : burnsideF42g_FixIn H X b)
    (hab : ∀ x ∈ X, x * a * x⁻¹ ≠ b ∧ x * a * x⁻¹ ≠ b * t)
    (hinv : ∀ w ∈ H, (w * w = 1 ∨ w * w = t) → w ≠ 1 → w ≠ t →
      ∃ k ∈ H, k⁻¹ * w * k ∈ X ∧ burnsideF42g_FixIn H X (k⁻¹ * w * k)) :
    H ≤ X := by
  obtain ⟨hN, hmem, hmk⟩ := burnsideF42g_quot_data htH htX hcen ht2
  set N := Subgroup.zpowers (⟨t, htH⟩ : ↥H) with hNdef
  set q := QuotientGroup.mk' N with hq
  set Xq := (X.subgroupOf H).map q with hXq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective N
  have haH : a ∈ H := hXH haX
  have hbH : b ∈ H := hXH hbX
  have hfix : ∀ c : ↥H, burnsideF42g_FixIn H X c → burnsideF42g_Fix1 Xq (q c) := by
    intro c hc k hk
    obtain ⟨k, rfl⟩ := hqs k
    rw [← map_inv, ← map_mul, ← map_mul, hmem] at hk
    rw [hmem]
    exact hc k k.2 hk
  have hqmul : ∀ y : ↥H, (y : M) * y = 1 → q y * q y = 1 := by
    intro y hy
    rw [← map_mul, ← map_one q]
    congr 1
    exact Subtype.ext hy
  refine fun h hh => (hmem ⟨h, hh⟩).mp ?_
  refine burnsideF42g_eq_top_of_fix1 (X := Xq) (a := q ⟨a, haH⟩) (b := q ⟨b, hbH⟩)
    ((hmem _).mpr hbX) (hqmul _ ha) (hqmul _ hb) (hfix _ hfa) (hfix _ hfb) ?_ ?_ (q ⟨h, hh⟩)
  · intro x hx hxab
    obtain ⟨x, hxX, rfl⟩ := hx
    rw [← map_inv, ← map_mul, ← map_mul, hmk] at hxab
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hxab
    rcases hxab with h1 | h1
    · exact (hab x hxX).1 h1.symm
    · apply (hab x hxX).2
      rw [h1, mul_assoc _ t t, ht2, mul_one]
  · intro w hw2 hw1
    obtain ⟨w, rfl⟩ := hqs w
    have hw2' : (w : M) * w = 1 ∨ (w : M) * w = t := by
      rw [← map_mul, ← map_one q, hmk] at hw2
      simp only [Subgroup.coe_one, one_mul, Subgroup.coe_mul] at hw2
      rcases hw2 with h1 | h1
      · exact Or.inl h1.symm
      · right
        calc (w : M) * w = (w * w * t) * t := by rw [mul_assoc _ t t, ht2, mul_one]
          _ = t := by rw [← h1, one_mul]
    have hw1' : (w : M) ≠ 1 ∧ (w : M) ≠ t := by
      constructor
      · intro h1
        apply hw1
        rw [show w = 1 from Subtype.ext h1, map_one]
      · intro h1
        apply hw1
        rw [← map_one q, hmk]
        right
        simp [h1, ht2]
    obtain ⟨k, hk, hkX, hkf⟩ := hinv w w.2 hw2' hw1'.1 hw1'.2
    refine ⟨q ⟨k, hk⟩, q (⟨k, hk⟩⁻¹ * w * ⟨k, hk⟩), (hmem _).mpr hkX, hfix _ hkf, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group

theorem burnsideF42g_le_of_fix1_central_mod {u v₁ v₂ : M} (htH : t ∈ H) (htX : t ∈ X)
    (hXH : X ≤ H) (hcen : ∀ h ∈ H, h * t = t * h) (ht2 : t * t = 1) (huX : u ∈ X)
    (hu : u * u = 1) (huc : ∀ x ∈ X, x * u * x⁻¹ = u ∨ x * u * x⁻¹ = u * t)
    (hfu : burnsideF42g_FixIn H X u) (hv₁X : v₁ ∈ X) (hv₁ : v₁ * v₁ = 1)
    (hf₁ : burnsideF42g_FixIn H X v₁) (h₁ : v₁ ≠ u ∧ v₁ ≠ u * t) (hv₂X : v₂ ∈ X)
    (hv₂ : v₂ * v₂ = 1) (hf₂ : burnsideF42g_FixIn H X v₂) (h₂ : v₂ ≠ u ∧ v₂ ≠ u * t)
    (hf₁₂ : burnsideF42g_FixIn H X (v₁ * v₂)) : H ≤ X := by
  obtain ⟨hN, hmem, hmk⟩ := burnsideF42g_quot_data htH htX hcen ht2
  set N := Subgroup.zpowers (⟨t, htH⟩ : ↥H) with hNdef
  set q := QuotientGroup.mk' N with hq
  set Xq := (X.subgroupOf H).map q with hXq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hfix : ∀ c : ↥H, burnsideF42g_FixIn H X c → burnsideF42g_Fix1 Xq (q c) := by
    intro c hc k hk
    obtain ⟨k, rfl⟩ := hqs k
    rw [← map_inv, ← map_mul, ← map_mul, hmem] at hk
    rw [hmem]
    exact hc k k.2 hk
  have hqmul : ∀ y : ↥H, (y : M) * y = 1 → q y * q y = 1 := by
    intro y hy
    rw [← map_mul, ← map_one q]
    congr 1
    exact Subtype.ext hy
  have hne : ∀ (v : M) (hv : v ∈ H), v ≠ u ∧ v ≠ u * t → q ⟨v, hv⟩ ≠ q ⟨u, hXH huX⟩ := by
    intro v hv hvu h1
    rw [hmk] at h1
    simp only at h1
    rcases h1 with h1 | h1
    · exact hvu.1 h1.symm
    · apply hvu.2
      rw [h1, mul_assoc, ht2, mul_one]
  refine fun h hh => (hmem ⟨h, hh⟩).mp ?_
  have hf₁₂' : burnsideF42g_Fix1 Xq (q ⟨v₁, hXH hv₁X⟩ * q ⟨v₂, hXH hv₂X⟩) := by
    rw [← map_mul]
    exact hfix ⟨v₁ * v₂, H.mul_mem (hXH hv₁X) (hXH hv₂X)⟩ hf₁₂
  refine burnsideF42g_eq_top_of_fix1_central (X := Xq) (a := q ⟨u, hXH huX⟩)
    ((hmem _).mpr huX) ?_ (hqmul _ hu) (hfix _ hfu)
    ((hmem _).mpr hv₁X) (hqmul _ hv₁) (hfix _ hf₁) (hne _ _ h₁)
    ((hmem _).mpr hv₂X) (hqmul _ hv₂) (hfix _ hf₂) (hne _ _ h₂) hf₁₂' (q ⟨h, hh⟩)
  intro x hx
  obtain ⟨x, hxX, rfl⟩ := hx
  rw [← map_mul, ← map_mul, hmk]
  simp only [Subgroup.coe_mul]
  have hxH : (x : M) ∈ H := x.2
  set x' : M := (x : M) with hx'
  rcases huc x hxX with h1 | h1
  · left
    calc u * x' = x' * u * x'⁻¹ * x' := by rw [h1]
      _ = x' * u := by group
  · right
    calc u * x' = (x' * u * x'⁻¹) * t * x' := by rw [h1, mul_assoc u t t, ht2, mul_one]
      _ = x' * u * x'⁻¹ * (t * x') := by group
      _ = x' * u * x'⁻¹ * (x' * t) := by rw [hcen x' hxH]
      _ = x' * u * t := by group
