module

public import CFSG.Quasithin.H13.A6S13821L32HatCaseII

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace L32HatStep

theorem two_group_eq_P0 {Q : Subgroup SL3.S} (hP : SL3.P0 ≤ Q) (h2 : IsPGroup 2 ↥Q) :
    Q = SL3.P0 := by
  have hT1 : L32HatSL3.T3X1.Nonempty := by decide
  have hT2 : L32HatSL3.T3X2.Nonempty := by decide
  have no3 : ∀ c : SL3.S, c ^ 3 = 1 → c ≠ 1 → c ∈ Q → False := by
    intro c hc3 hc1 hcQ
    obtain ⟨k, hk⟩ := h2 ⟨c, hcQ⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact hc1 (eq_one_of_pow_three_pow_two hc3 hk')
  rcases SL3.overgroups_SL3 Q hP with h | h | h | h
  · exact h
  · exfalso
    obtain ⟨c, hc⟩ := hT1
    simp only [L32HatSL3.T3X1, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    exact no3 c hc.2.1 hc.2.2 (by rw [h]; exact hc.1)
  · exfalso
    obtain ⟨c, hc⟩ := hT2
    simp only [L32HatSL3.T3X2, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    exact no3 c hc.2.1 hc.2.2 (by rw [h]; exact hc.1)
  · exfalso
    obtain ⟨c, hc⟩ := hT1
    simp only [L32HatSL3.T3X1, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    exact no3 c hc.2.1 hc.2.2 (by rw [h]; exact Subgroup.mem_top c)

theorem le_P0_of_normal_two {X Y : Subgroup SL3.S} (hX : X = SL3.X1 ∨ X = SL3.X2)
    (hYX : Y ≤ X) (hYn : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) (hY2 : IsPGroup 2 ↥Y) :
    Y ≤ SL3.P0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP0X : SL3.P0 ≤ X := by
    rcases hX with rfl | rfl
    · exact inf_le_left
    · exact inf_le_right
  set Yc : Subgroup ↥X := Y.subgroupOf X with hYc
  haveI hYcn : Yc.Normal := ⟨fun n hn g => by
    rw [hYc, Subgroup.mem_subgroupOf] at hn ⊢
    have := hYn (g : SL3.S) g.2 _ hn
    simpa using this⟩
  have hYc2 : IsPGroup 2 ↥Yc := by
    intro n
    obtain ⟨k, hk⟩ := hY2 ⟨((n : ↥X) : SL3.S), Subgroup.mem_subgroupOf.mp n.2⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  set P0c : Subgroup ↥X := SL3.P0.subgroupOf X with hP0c
  have hP0c2 : IsPGroup 2 ↥P0c := by
    intro g
    obtain ⟨k, hk⟩ := SL3.P0_sylow.1 ⟨((g : ↥X) : SL3.S), Subgroup.mem_subgroupOf.mp g.2⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hP0c2
  set Qi : Subgroup SL3.S := ((Q : Subgroup ↥X)).map X.subtype with hQi
  have hQi2 : IsPGroup 2 ↥Qi := by
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp g.2
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨x, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : ((x : ↥X) : SL3.S) ^ 2 ^ k = 1 := by
      have h := congrArg Subtype.val hk
      have h' := congrArg Subtype.val h
      simpa using h'
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hxg]
    exact h1
  have hP0Qi : SL3.P0 ≤ Qi := by
    intro p hp
    have hpX : (⟨p, hP0X hp⟩ : ↥X) ∈ P0c := Subgroup.mem_subgroupOf.mpr hp
    exact Subgroup.mem_map.mpr ⟨⟨p, hP0X hp⟩, hQ hpX, rfl⟩
  have hQi_eq : Qi = SL3.P0 := two_group_eq_P0 hP0Qi hQi2
  have hYcQ : Yc ≤ (Q : Subgroup ↥X) := IsPGroup.le_sylow_of_normal hYc2 Q
  intro y hy
  have hyc : (⟨y, hYX hy⟩ : ↥X) ∈ Yc := Subgroup.mem_subgroupOf.mpr hy
  have hyQ := hYcQ hyc
  have hyQi : y ∈ Qi := Subgroup.mem_map.mpr ⟨⟨y, hYX hy⟩, hyQ, rfl⟩
  rw [hQi_eq] at hyQi
  exact hyQi

@[expose] def coreF1 : Finset SL3.S :=
  Finset.univ.filter fun p => SL3.InX1 p ∧ SL3.InX2 p ∧
    ∀ x : SL3.S, SL3.InX1 x → SL3.InX1 (x * p * x⁻¹) ∧ SL3.InX2 (x * p * x⁻¹)

@[expose] def coreF2 : Finset SL3.S :=
  Finset.univ.filter fun p => SL3.InX1 p ∧ SL3.InX2 p ∧
    ∀ x : SL3.S, SL3.InX2 x → SL3.InX1 (x * p * x⁻¹) ∧ SL3.InX2 (x * p * x⁻¹)

theorem coreF1_card : coreF1.card ≤ 4 := by decide +kernel

theorem coreF2_card : coreF2.card ≤ 4 := by decide +kernel

theorem card_le_four_of_normal {X Y : Subgroup SL3.S} (hX : X = SL3.X1 ∨ X = SL3.X2)
    (hYX : Y ≤ X) (hYn : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) (hY2 : IsPGroup 2 ↥Y) :
    Nat.card Y ≤ 4 := by
  have hYP0 := le_P0_of_normal_two hX hYX hYn hY2
  have hsub : ∀ (C : Finset SL3.S), (∀ y ∈ Y, y ∈ C) → Nat.card Y ≤ C.card := by
    intro C hC
    have h1 : (Y : Set SL3.S) ⊆ (C : Set SL3.S) := fun y hy => by
      simpa using hC y hy
    have h2 := Set.ncard_le_ncard h1 (Finset.finite_toSet C)
    rw [Set.ncard_coe_finset] at h2
    have hcard : Nat.card Y = (Y : Set SL3.S).ncard := Nat.card_coe_set_eq (Y : Set SL3.S)
    rw [hcard]
    exact h2
  rcases hX with rfl | rfl
  · refine le_trans (hsub coreF1 ?_) coreF1_card
    intro y hy
    have hyP := hYP0 hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyP.1, hyP.2, fun x hx => ?_⟩
    have hxy := hYn x hx y hy
    have := hYP0 hxy
    exact ⟨this.1, this.2⟩
  · refine le_trans (hsub coreF2 ?_) coreF2_card
    intro y hy
    have hyP := hYP0 hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyP.1, hyP.2, fun x hx => ?_⟩
    have hxy := hYn x hx y hy
    have := hYP0 hxy
    exact ⟨this.1, this.2⟩

theorem X1_not_le_X2 : ¬ (SL3.X1 ≤ SL3.X2) := by
  intro h
  have hne : L32HatSL3.T3X1.Nonempty := by decide
  obtain ⟨c, hc⟩ := hne
  have hcX1 : SL3.InX1 c := (Finset.mem_filter.mp hc).2.1
  exact L32HatSL3.T3X1_not_InX2 c hc (h (show c ∈ SL3.X1 from hcX1))

theorem X2_not_le_X1 : ¬ (SL3.X2 ≤ SL3.X1) := by
  intro h
  have hne : L32HatSL3.T3X2.Nonempty := by decide
  obtain ⟨c, hc⟩ := hne
  have hcX2 : SL3.InX2 c := (Finset.mem_filter.mp hc).2.1
  exact L32HatSL3.T3X2_not_InX1 c hc (h (show c ∈ SL3.X2 from hcX2))

end L32HatStep

end CFSG.Quasithin.H13.A6
