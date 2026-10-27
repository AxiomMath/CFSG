module

public import CFSG.Quasithin.Background.C124YLH6LiftA5
public import CFSG.Quasithin.Background.C124YLH6Lift
public import CFSG.Quasithin.Background.C124YLH6Ov

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL.H6

open Equiv Subgroup CFSG.Quasithin.C124.YL.A6

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_A5_of_hat (q : Γ →* P6) (hq : q.range = alternatingGroup (Fin 6))
    (hker3 : Nat.card q.ker = 3) (hkc : q.ker ≤ Subgroup.center Γ) {K : Subgroup Γ}
    (hK4 : Nat.card K = 4) (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hsq : ∀ a ∈ K, a * a = 1) :
    ∃ Y : Subgroup Γ, K ≤ Y ∧ Nat.card Y = 60 ∧ Nonempty (↥Y ≃* alternatingGroup (Fin 5)) ∧
      Y ⊔ Subgroup.normalizer (K : Set Γ) = ⊤ := by
  have hKbA : K.map q ≤ alternatingGroup (Fin 6) := hq ▸ Subgroup.map_le_range q K
  have hKcomm : ∀ a ∈ K.map q, ∀ b ∈ K.map q, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hKsq : ∀ a ∈ K.map q, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq a ha, map_one]
  obtain ⟨Yb, hYbA, hKY, hYb60, hYbA5, n, hnA, hnN, hnY⟩ :=
    klein_overgroup hKbA (image_klein hker3 hK4 hsq) hKcomm hKsq
  obtain ⟨e5⟩ := hYbA5
  let Hh : Subgroup Γ := Yb.comap q
  have hker_le : q.ker ≤ Hh := fun z hz => by
    show q z ∈ Yb
    rw [MonoidHom.mem_ker.1 hz]
    exact Yb.one_mem
  have hmapH : Hh.map q = Yb := Subgroup.map_comap_eq_self (hq ▸ hYbA)
  have hcardH : Nat.card Hh = 180 := by
    rw [card_eq_map_mul_inf_ker q Hh, hmapH, hYb60, inf_eq_left.2 hker_le, hker3]
  have hKH : K ≤ Hh := fun k hk => hKY (Subgroup.mem_map_of_mem q hk)
  let Y : Subgroup Γ := ⁅Hh, Hh⁆
  have hYH : Y ≤ Hh := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact Hh.mul_mem (Hh.mul_mem (Hh.mul_mem h₁ h₂) (Hh.inv_mem h₁)) (Hh.inv_mem h₂)
  have hmapY : Y.map q = Yb := by
    rw [Subgroup.map_commutator, hmapH]
    exact commutator_eq_self_of_equiv_alt_five e5
  have hzY : ∀ z ∈ q.ker, z ≠ 1 → z ∉ Y := by
    intro z hz hz1
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let S : Sylow 3 ↥Hh := default
    have hS : Nat.card S = 3 ^ 2 := by
      rw [Sylow.card_eq_multiplicity, hcardH, Nat.factorization_def _ Nat.prime_three]
      have h9 : padicValNat 3 180 = 2 := by decide +kernel
      rw [h9]
    have hcomm : IsMulCommutative (S : Subgroup ↥Hh) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq hS
    have hidx : (S : Subgroup ↥Hh).index = 20 := by
      have h := Subgroup.index_mul_card (S : Subgroup ↥Hh)
      rw [hS, hcardH] at h
      omega
    exact central_not_mem_commutator_sub Hh S z (hker_le hz) (hkc hz)
      (by rw [orderOf_eq_three hker3 hz hz1, hidx]; norm_num) hz1
  have hYker : ∀ z ∈ q.ker ⊓ Y, z = 1 := fun z hz => by_contra fun h => hzY z hz.1 h hz.2
  have hcardY : Nat.card Y = 60 := by
    rw [card_eq_map_mul_inf_ker q Y, hmapY, hYb60]
    have : q.ker ⊓ Y = ⊥ := eq_bot_iff.2 fun z hz => Subgroup.mem_bot.2 (hYker z hz)
    rw [this, Subgroup.card_bot]
  have hinjY : Function.Injective (q.comp Y.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    have h1 : (a : Γ) ∈ q.ker := ha
    exact Subgroup.mem_bot.2 (Subtype.ext (hYker a ⟨h1, a.2⟩))
  have hrangeY : (q.comp Y.subtype).range = Yb := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmapY]
  have hYA5 : Nonempty (↥Y ≃* alternatingGroup (Fin 5)) :=
    ⟨((MonoidHom.ofInjective hinjY).trans (MulEquiv.subgroupCongr hrangeY)).trans e5⟩
  have hKY' : K ≤ Y := by
    intro k hk
    have hqk : q k ∈ Y.map q := hmapY ▸ hKY (Subgroup.mem_map_of_mem q hk)
    obtain ⟨y, hy, hqy⟩ := hqk
    have hz'ker : k * y⁻¹ ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqy]
      simp
    have hcz := Subgroup.mem_center_iff.1 (hkc hz'ker) k
    have hzz : (k * y⁻¹) * (k * y⁻¹) = (y * y)⁻¹ := by
      calc (k * y⁻¹) * (k * y⁻¹) = (k * y⁻¹ * k) * y⁻¹ := by group
        _ = (k * (k * y⁻¹)) * y⁻¹ := by rw [hcz]
        _ = (k * k) * (y⁻¹ * y⁻¹) := by group
        _ = (y * y)⁻¹ := by rw [hsq k hk]; group
    have hzzY : (k * y⁻¹) * (k * y⁻¹) ∈ q.ker ⊓ Y :=
      ⟨q.ker.mul_mem hz'ker hz'ker, hzz ▸ Y.inv_mem (Y.mul_mem hy hy)⟩
    have hzz1 := hYker _ hzzY
    have hz'1 : k * y⁻¹ = 1 := eq_one_of_ker_sq hker3 hz'ker hzz1
    have : k = y := by
      have := congrArg (· * y) hz'1
      simpa using this
    rw [this]
    exact hy
  refine ⟨Y, hKY', hcardY, hYA5, ?_⟩
  obtain ⟨ν, hν⟩ : ∃ ν : Γ, q ν = n := by
    have : n ∈ q.range := hq ▸ hnA
    exact this
  have hνN : ν ∈ Subgroup.normalizer (K : Set Γ) :=
    klein_normalizes hker3 hkc hsq fun k hk => by
      rw [hν]
      exact hnN (q k) (Subgroup.mem_map_of_mem q hk)
  have hkerN : q.ker ≤ Subgroup.normalizer (K : Set Γ) := fun z hz => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc := Subgroup.mem_center_iff.1 (hkc hz) h
    have : z * h * z⁻¹ = h := by rw [← hc]; group
    rw [this]
  set M := Y ⊔ Subgroup.normalizer (K : Set Γ) with hM
  have h1 : Yb ≤ M.map q := hmapY ▸ Subgroup.map_mono le_sup_left
  have h2 : n ∈ M.map q := ⟨ν, Subgroup.mem_sup_right hνN, hν⟩
  have hidxY : (Yb.subgroupOf (alternatingGroup (Fin 6))).index = 6 := by
    have h := Subgroup.index_mul_card (Yb.subgroupOf (alternatingGroup (Fin 6)))
    rw [card_subgroupOf_A6 hYbA, hYb60, card_Gam] at h
    omega
  have h3 : (M.map q).subgroupOf (alternatingGroup (Fin 6)) = ⊤ := by
    refine eq_top_of_index_six (by rw [card_Gam]; norm_num) hidxY (fun x hx => h1 hx) ?_
    intro heq
    have : (⟨n, hnA⟩ : Gam) ∈ (M.map q).subgroupOf (alternatingGroup (Fin 6)) := h2
    rw [← heq] at this
    exact hnY this
  rw [eq_top_iff]
  intro x _
  have hxA : q x ∈ alternatingGroup (Fin 6) := hq ▸ ⟨x, rfl⟩
  have hx : q x ∈ M.map q := by
    have : (⟨q x, hxA⟩ : Gam) ∈ (M.map q).subgroupOf (alternatingGroup (Fin 6)) := by
      rw [h3]
      trivial
    exact this
  obtain ⟨m, hm, hqm⟩ := hx
  have hxm : x * m⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqm]
    simp
  have : x * m⁻¹ ∈ M := Subgroup.mem_sup_right (hkerN hxm)
  have := M.mul_mem this hm
  simpa using this

end CFSG.Quasithin.C124.YL.H6
