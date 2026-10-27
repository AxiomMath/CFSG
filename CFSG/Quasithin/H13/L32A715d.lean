module

public import CFSG.Quasithin.H13.L32A715b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem exists_y_of_faithful {Γ : Type*} [Group Γ] [Finite Γ] {X L1s Ts : Subgroup Γ}
    [hXn : X.Normal] (hK : IsPOnePlusTwo 3 ↥X) (hL1X : L1s ≤ X) (hL1n : L1s.Normal)
    (hcard3 : Nat.card L1s = 3) (hTs2 : IsPGroup 2 ↥Ts)
    (hfaith' : ∀ g ∈ Ts, (∀ x ∈ X, g * x = x * g) → g = 1)
    (hirr' : ∀ W : Subgroup Γ, L1s ≤ W → W ≤ X → Ts ≤ Subgroup.normalizer (W : Set Γ) →
      W = L1s ∨ W = X)
    (hnot' : ∃ t ∈ Ts, t ∉ Subgroup.centralizer (L1s : Set Γ)) :
    (Subgroup.center ↥X).map X.subtype = L1s ∧
    ∃ y ∈ Ts, y ∈ Subgroup.centralizer (L1s : Set Γ) ∧ y ^ 2 ≠ 1 ∧ y ^ 4 = 1 ∧
      (∀ r ∈ Ts, r ∈ Subgroup.centralizer (L1s : Set Γ) → r ^ 2 = 1 → r ≠ 1 → r = y ^ 2) ∧
      (∀ x ∈ X, y ^ 2 * x * (y ^ 2)⁻¹ * x ∈ L1s) ∧
      (∀ W : Subgroup Γ, L1s ≤ W → W ≤ X → (∀ w ∈ W, y * w * y⁻¹ ∈ W) →
        W = L1s ∨ W = X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : (Subgroup.center ↥X).map X.subtype = L1s :=
    center_eq_of_normal_card_three hK hL1X hL1n hcard3
  refine ⟨hcen, ?_⟩
  set ρ : Γ →* MulAut ↥X := MulAut.conjNormal with hρdef
  have hρ : ∀ (g : Γ) (x : ↥X), ((ρ g x : ↥X) : Γ) = g * x * g⁻¹ := fun g x =>
    MulAut.conjNormal_apply g x
  have hmemZ : ∀ x : ↥X, x ∈ Subgroup.center ↥X ↔ (x : Γ) ∈ L1s := by
    intro x
    rw [← hcen]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  have hfixZ : ∀ g : Γ, (∀ z ∈ Subgroup.center ↥X, ρ g z = z) ↔
      g ∈ Subgroup.centralizer (L1s : Set Γ) := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h z hz
      have hzX := hL1X hz
      have h1 := congrArg Subtype.val (h ⟨z, hzX⟩ ((hmemZ ⟨z, hzX⟩).mpr hz))
      rw [hρ] at h1
      calc z * g = g * z * g⁻¹ * g := by rw [h1]
        _ = g * z := by group
    · intro h z hz
      apply Subtype.ext
      rw [hρ, ← h z ((hmemZ z).mp hz)]
      group
  have hfaith : ∀ g ∈ Ts, ρ g = 1 → g = 1 := by
    intro g hg h1
    refine hfaith' g hg fun x hx => ?_
    have h2 := congrArg Subtype.val (congrArg (fun φ : MulAut ↥X => φ ⟨x, hx⟩) h1)
    simp only [MulAut.one_apply] at h2
    rw [hρ] at h2
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h2]
  set 𝒯 := Ts.map ρ with h𝒯def
  have h𝒯 : IsPGroup 2 ↥𝒯 := hTs2.map ρ
  have hirr : ∀ W : Subgroup ↥X, Subgroup.center ↥X ≤ W → (∀ t ∈ 𝒯, ∀ w ∈ W, t w ∈ W) →
      W = Subgroup.center ↥X ∨ W = ⊤ := by
    intro W hZW hW
    have hZW' : L1s ≤ W.map X.subtype := by
      rw [← hcen]
      exact Subgroup.map_mono hZW
    have hTW' : Ts ≤ Subgroup.normalizer ((W.map X.subtype : Subgroup Γ) : Set Γ) := by
      have key : ∀ t ∈ Ts, ∀ w ∈ W.map X.subtype, t * w * t⁻¹ ∈ W.map X.subtype := by
        intro t ht w hw
        obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
        exact ⟨ρ t w', hW _ ⟨t, ht, rfl⟩ w' hw', hρ t w'⟩
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · exact key t ht w
      · intro h
        have := key t⁻¹ (Ts.inv_mem ht) _ h
        simpa [mul_assoc] using this
    rcases hirr' (W.map X.subtype) hZW' (Subgroup.map_subtype_le W) hTW' with he | he
    · left
      apply Subgroup.map_injective X.subtype_injective
      rw [he, hcen]
    · right
      apply Subgroup.map_injective X.subtype_injective
      rw [he, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hnot : ∃ t ∈ 𝒯, ¬ ∀ z ∈ Subgroup.center ↥X, t z = z := by
    obtain ⟨t, ht, htC⟩ := hnot'
    exact ⟨ρ t, ⟨t, ht, rfl⟩, fun h => htC ((hfixZ t).mp h)⟩
  obtain ⟨y', hy'𝒯, hy'Z, hy'2, hy'4⟩ := Heis.exists_order_four hK h𝒯 hirr hnot
  obtain ⟨y, hyT, rfl⟩ := Subgroup.mem_map.mp hy'𝒯
  have hyC : y ∈ Subgroup.centralizer (L1s : Set Γ) := (hfixZ y).mp hy'Z
  have hy4 : y ^ 4 = 1 :=
    hfaith _ (Ts.pow_mem hyT 4) (by rw [map_pow]; exact hy'4)
  have hy2 : y ^ 2 ≠ 1 := fun h => hy'2 (by rw [← map_pow, h, map_one])
  have hr2 : ρ (y ^ 2) * ρ (y ^ 2) = 1 := by
    rw [← map_mul, ← pow_add]
    exact (by rw [show 2 + 2 = 4 by norm_num, hy4, map_one])
  have hrZ : ∀ z ∈ Subgroup.center ↥X, ρ (y ^ 2) z = z :=
    (hfixZ _).mpr (Subgroup.pow_mem _ hyC 2)
  have hrne : ρ (y ^ 2) ≠ 1 := fun h => hy2 (hfaith _ (Ts.pow_mem hyT 2) h)
  have hrinv := Heis.inverts_of_involution hK hr2 hrZ hrne
  refine ⟨y, hyT, hyC, hy2, hy4, ?_, ?_, ?_⟩
  ·
    intro r hrT hrC hr2' hr1
    have h1 : ρ r * ρ r = 1 := by rw [← map_mul, ← sq, hr2', map_one]
    have h2 : ∀ z ∈ Subgroup.center ↥X, ρ r z = z := (hfixZ r).mpr hrC
    have h3 : ρ r ≠ 1 := fun h => hr1 (hfaith r hrT h)
    obtain ⟨m, hm⟩ := hTs2 ⟨r * y ^ 2, Ts.mul_mem hrT (Ts.pow_mem hyT 2)⟩
    have hm' : (ρ r * ρ (y ^ 2)) ^ 2 ^ m = 1 := by
      rw [← map_mul, ← map_pow]
      have := congrArg Subtype.val hm
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [this, map_one]
    have he := Heis.eq_of_involutions hK h1 hr2 h2 hrZ h3 hrne hm'
    have h4 : ρ (r * (y ^ 2)⁻¹) = 1 := by rw [map_mul, map_inv, he, mul_inv_cancel]
    have h5 := hfaith _ (Ts.mul_mem hrT (Ts.inv_mem (Ts.pow_mem hyT 2))) h4
    exact mul_inv_eq_one.mp h5
  ·
    intro x hx
    have h1 := hrinv ⟨x, hx⟩
    rw [hmemZ, Subgroup.coe_mul, hρ] at h1
    exact h1
  ·
    intro W hLW hWX hyW
    by_contra hne
    push Not at hne
    have hψZ : ∀ z ∈ Subgroup.center ↥X, ρ y z = z := hy'Z
    have hψ4 : (ρ y) ^ 4 = 1 := by rw [← map_pow, hy4, map_one]
    have hψ2 : (ρ y) ^ 2 ≠ 1 := hy'2
    set W' := W.subgroupOf X with hW'
    have hZW' : Subgroup.center ↥X ≤ W' := fun z hz =>
      Subgroup.mem_subgroupOf.mpr (hLW ((hmemZ z).mp hz))
    have hW'Z : W' ≠ Subgroup.center ↥X := by
      intro h
      apply hne.1
      apply le_antisymm _ hLW
      intro w hw
      have h1 : (⟨w, hWX hw⟩ : ↥X) ∈ W' := Subgroup.mem_subgroupOf.mpr hw
      rw [h] at h1
      exact (hmemZ _).mp h1
    have hW't : W' ≠ ⊤ := by
      intro h
      apply hne.2
      refine le_antisymm hWX fun x hx => ?_
      have h1 : (⟨x, hx⟩ : ↥X) ∈ W' := h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h1
    refine Heis.not_invariant_of_order_four hK hψZ hψ4 hψ2 hZW' hW'Z hW't fun w hw => ?_
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [hρ]
    exact hyW _ (Subgroup.mem_subgroupOf.mp hw)


end CFSG.Quasithin.H13.L32A
