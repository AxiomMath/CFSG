module

public import CFSG.Sporadic.Recognition.LyonsModelCP

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly0

open Equiv Subgroup

structure ModelChecks : Prop where
  tab : tabCheck = true
  cover : coverCheck = true
  struct : structCheck = true
  cp1 : cp1Check = true
  inv : invCheck = true
  mark : markCheck = true
  cp3 : Cp3Fact

@[expose] noncomputable def conjEquiv {B : Type*} [Group B] (ν : B ≃* B0) (g : B0) : B ≃* B0 :=
  ν.trans (MulAut.conj g)

theorem conjEquiv_apply {B : Type*} [Group B] (ν : B ≃* B0) (g : B0) (b : B) :
    conjEquiv ν g b = g * ν b * g⁻¹ := rfl


section Facts

variable (hM : ModelChecks)
include hM

theorem K0_normal : K0.Normal := (K0_normal_index_le_two hM.tab hM.struct).1

theorem conj_xB (b : B0) : b * xB * b⁻¹ = xB ∨ b * xB * b⁻¹ = xB⁻¹ := by
  by_cases hb : b ∈ K0
  · left
    have := (K0_centralizer_and_inv hM.tab hM.cover hM.struct).1
    rw [this] at hb
    have h1 := Subgroup.mem_centralizer_iff.1 hb xB (Set.mem_singleton xB)
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  · exact Or.inr ((K0_centralizer_and_inv hM.tab hM.cover hM.struct).2 b hb)

theorem comm_xB_of_mem_K0 {b : B0} (hb : b ∈ K0) : b * xB = xB * b := by
  have := (K0_centralizer_and_inv hM.tab hM.cover hM.struct).1
  rw [this] at hb
  exact (Subgroup.mem_centralizer_iff.1 hb xB (Set.mem_singleton xB)).symm

theorem mem_K0_of_pow_three {u : B0} (hu : u ^ 3 = 1) : u ∈ K0 := by
  have hn := K0_normal hM
  have h1 : u ^ K0.index ∈ K0 := Subgroup.pow_index_mem K0 u
  rw [K0_index_two hM.tab hM.cover hM.struct] at h1
  have : u = (u ^ 2)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ']
    exact hu
  rw [this]
  exact inv_mem h1

theorem map_eq_xB_or_inv {B : Type*} [Group B] {a : B} (h3 : orderOf a = 3)
    (hn : (zpowers a).Normal) (ν : B ≃* B0) : ν a = xB ∨ ν a = xB⁻¹ := by
  have hu3 : orderOf (ν a) = 3 := by rw [MulEquiv.orderOf_eq]; exact h3
  have hnu : (zpowers (ν a)).Normal := by
    have : (zpowers a).map ν.toMonoidHom = zpowers (ν a) := by
      rw [MonoidHom.map_zpowers]; rfl
    rw [← this]
    exact Subgroup.Normal.map hn ν.toMonoidHom ν.surjective
  have hperf := isPerfect_K0 hM.tab hM.cover hM.struct
  have hcomm := commute_of_normal_zpowers K0 hnu
  have hupow : ν a ^ 3 = 1 := by rw [← hu3]; exact pow_orderOf_eq_one _
  have huK : ν a ∈ K0 := mem_K0_of_pow_three hM hupow
  have hmem : ν a ∈ zpowers xB := K0_center hM.tab hM.cover hM.struct (ν a) huK hcomm
  obtain ⟨n, hn'⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hx3 : xB ^ 3 = 1 := xB_pow_three hM.tab hM.struct
  have hne : ν a ≠ 1 := by
    intro h1
    have : a = 1 := ν.injective (by rw [h1, map_one])
    rw [this, orderOf_one] at h3
    omega
  rcases zpow_cases hx3 n with h1 | h1 | h1
  · exact absurd (by rw [← hn', h1]) hne
  · left; rw [← hn', h1]
  · right
    rw [← hn', h1]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact hx3

theorem exists_equiv_map_eq_xB {B : Type*} [Group B] {a : B} (h3 : orderOf a = 3)
    (hn : (zpowers a).Normal) (ν : B ≃* B0) : ∃ ν' : B ≃* B0, ν' a = xB := by
  rcases map_eq_xB_or_inv hM h3 hn ν with h | h
  · exact ⟨ν, h⟩
  · refine ⟨conjEquiv ν cB, ?_⟩
    rw [conjEquiv_apply, h]
    have h1 := cB_xB hM.tab hM.struct
    calc cB * xB⁻¹ * cB⁻¹ = (cB * xB * cB⁻¹)⁻¹ := by group
      _ = xB := by rw [h1, inv_inv]

end Facts


section Lines

variable (hM : ModelChecks)
include hM

theorem gB_xB : gB * xB * gB⁻¹ = xB⁻¹ := by
  obtain ⟨e, -⟩ := invCheck_spec hM.tab hM.struct hM.inv
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, coe_xB, coe_gB,
    mul_assoc]
  exact e

theorem gB_yB : gB * yB * gB⁻¹ = yB ∨ gB * yB * gB⁻¹ = yB⁻¹ := by
  obtain ⟨-, e, -⟩ := invCheck_spec hM.tab hM.struct hM.inv
  rcases e with e | e
  · left
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_yB, coe_gB, mul_assoc]
    exact e
  · right
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, coe_yB, coe_gB,
      mul_assoc]
    exact e

theorem gB_wB : gB * wB * gB⁻¹ = wB ∨ gB * wB * gB⁻¹ = wB⁻¹ := by
  obtain ⟨-, -, e, -⟩ := invCheck_spec hM.tab hM.struct hM.inv
  rcases e with e | e
  · left
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_wB, coe_gB, mul_assoc]
    exact e
  · right
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, coe_wB, coe_gB,
      mul_assoc]
    exact e

theorem conj_yB_of_mem_Y0 {b : B0} (hb : b ∈ Y0) :
    b * yB * b⁻¹ = yB ∨ b * yB * b⁻¹ = yB⁻¹ := by
  have hb' := (mem_Y0_iff hM.tab hM.struct hM.cp1).1 hb
  rcases conj_y0G_of_mem_normalizer hM.tab hM.struct hM.cp1 hb' with e | e
  · left
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_yB]
    exact e
  · right
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, coe_yB]
    exact e

end Lines

theorem card_normalizer_zpowers_of_equiv {A A' : Type*} [Group A] [Group A'] (ν : A ≃* A')
    (a : A) :
    Nat.card ↥(normalizer (zpowers (ν a) : Set A')) =
      Nat.card ↥(normalizer (zpowers a : Set A)) := by
  have e : (normalizer (zpowers a : Set A)).map ν.toMonoidHom =
      normalizer (zpowers (ν a) : Set A') := by
    rw [map_equiv_normalizer_eq, MonoidHom.map_zpowers]; rfl
  rw [← e, Subgroup.card_map_of_injective ν.injective]

section Stage

variable (hM : ModelChecks)
include hM

theorem exists_equiv_lines {B : Type*} [Group B] {x₁ x₂ x₃ u : B} (ν : B ≃* B0)
    (h1 : ν x₁ = xB) (h2 : ν x₂ = yB) (hu : u * x₂ * u⁻¹ = x₃) (hc : x₃ * x₂ = x₂ * x₃)
    (hne1 : x₃ ≠ x₂) (hne2 : x₃ ≠ x₂⁻¹)
    (hN : Nat.card ↥(normalizer (zpowers x₂ : Set B)) = 349920) :
    ∃ ν' : B ≃* B0, (ν' x₁ = xB ∨ ν' x₁ = xB⁻¹) ∧ (ν' x₂ = yB ∨ ν' x₂ = yB⁻¹) ∧
      (ν' x₃ = wB ∨ ν' x₃ = wB⁻¹) := by
  have hw' : ν x₃ = ν u * yB * (ν u)⁻¹ := by
    rw [← hu, map_mul, map_mul, map_inv, h2]
  have hy : ν x₃ * yB = yB * ν x₃ := by
    rw [← h2, ← map_mul, ← map_mul, hc]
  have hne1' : ν x₃ ≠ yB := by
    rw [← h2]; intro e; exact hne1 (ν.injective e)
  have hne2' : ν x₃ ≠ yB⁻¹ := by
    rw [← h2, ← map_inv]; intro e; exact hne2 (ν.injective e)
  have hN' : Nat.card ↥(normalizer (zpowers yB : Set B0)) = 349920 := by
    rw [← h2, card_normalizer_zpowers_of_equiv, hN]
  obtain ⟨u', hu', hres⟩ := cp3_model hM.tab hM.cover hM.struct hM.cp1 hM.cp3 hw' hy hne1' hne2' hN'
  refine ⟨conjEquiv ν u', ?_, ?_, ?_⟩
  · rw [conjEquiv_apply, h1]
    exact conj_xB hM u'
  · rw [conjEquiv_apply, h2]
    exact conj_yB_of_mem_Y0 hM (UY_le_Y0 hM.tab hM.struct hM.cp1 hM.inv hu')
  · rw [conjEquiv_apply]
    exact hres

theorem exists_equiv_sign {B : Type*} [Group B] {x₁ x₂ x₃ : B} (ν : B ≃* B0)
    (h1 : ν x₁ = xB ∨ ν x₁ = xB⁻¹) (h2 : ν x₂ = yB ∨ ν x₂ = yB⁻¹)
    (h3 : ν x₃ = wB ∨ ν x₃ = wB⁻¹) :
    ∃ φ : B ≃* B0, φ x₁ = xB ∧ (φ x₂ = yB ∨ φ x₂ = yB⁻¹) ∧ (φ x₃ = wB ∨ φ x₃ = wB⁻¹) := by
  rcases h1 with h1 | h1
  · exact ⟨ν, h1, h2, h3⟩
  · refine ⟨conjEquiv ν gB, ?_, ?_, ?_⟩
    · rw [conjEquiv_apply, h1]
      have := gB_xB hM
      calc gB * xB⁻¹ * gB⁻¹ = (gB * xB * gB⁻¹)⁻¹ := by group
        _ = xB := by rw [this, inv_inv]
    · rw [conjEquiv_apply]
      rcases h2 with e | e
      · rw [e]; exact gB_yB hM
      · rw [e]
        rcases gB_yB hM with e' | e'
        · right
          calc gB * yB⁻¹ * gB⁻¹ = (gB * yB * gB⁻¹)⁻¹ := by group
            _ = yB⁻¹ := by rw [e']
        · left
          calc gB * yB⁻¹ * gB⁻¹ = (gB * yB * gB⁻¹)⁻¹ := by group
            _ = yB := by rw [e', inv_inv]
    · rw [conjEquiv_apply]
      rcases h3 with e | e
      · rw [e]; exact gB_wB hM
      · rw [e]
        rcases gB_wB hM with e' | e'
        · right
          calc gB * wB⁻¹ * gB⁻¹ = (gB * wB * gB⁻¹)⁻¹ := by group
            _ = wB⁻¹ := by rw [e']
        · left
          calc gB * wB⁻¹ * gB⁻¹ = (gB * wB * gB⁻¹)⁻¹ := by group
            _ = wB := by rw [e', inv_inv]

end Stage

end CFSG.Sporadic.Recognition.LyonsSims.Ly0
