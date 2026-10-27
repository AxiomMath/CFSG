module

public import CFSG.Quasithin.Vol2.Ch11SecOE8O
public import CFSG.Quasithin.Vol2.Ch11SecOE8N

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

namespace L3T

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257
  CFSG.QuasithinUnique.Fin257.L3

variable {F : Type} [Field F] [CharP F 2]

theorem twisted_case [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (E : Subgroup (MulAut (projectiveSL 3 F))) (h2 : ∀ α ∈ E, α * α = 1)
    (hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α)
    (hU : ∀ α ∈ E, ∀ u ∈ projUnitriangular 3 F, α u ∈ projUnitriangular 3 F)
    {θ : MulAut (projectiveSL 3 F)} (hθE : θ ∉ semilinearAutGroup 3 F)
    (hθU : ∀ u ∈ projUnitriangular 3 F, θ u ∈ projUnitriangular 3 F)
    (hθc : ∀ α ∈ E, θ * α = α * θ) (hcard : Nat.card F < Nat.card E) :
    E.comap (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) ≤ Wg ∧
      E.comap (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) ≠ ⊥ ∧
      ∃ a ∈ E, a ∉ semilinearAutGroup 3 F ∧
        ∀ g ∈ (Wg : Subgroup (projectiveSL 3 F)), a g = g := by
  set c : projectiveSL 3 F →* MulAut (projectiveSL 3 F) := MulAut.conj with hcdef
  have hinj : Function.Injective c := conj_injective_of_center center_trivial_M
  set B := E.comap c with hB
  obtain ⟨hB2, hBU⟩ := comap_conj_le_U (modelData_L3 hn hF) E h2 hU
  have hBV : B ≤ V1 ∨ B ≤ V2 := elem_le_V1_or_V2 hBU hB2
  have hfixE : ∀ α ∈ E, ∀ g ∈ B, α g = g := fun α hα g hg =>
    fixes_of_comm hinj (hc α hα _ hg)
  have hfixθ : ∀ g ∈ B, θ g = g := fun g hg => fixes_of_comm hinj (hθc _ hg)
  obtain ⟨hV1, hV2⟩ := map_V_of_not_mem_semilinear hθE hθU
  have hBW : B ≤ (Wg : Subgroup (projectiveSL 3 F)) := by
    rw [← V1_inf_V2]
    rcases hBV with h | h
    · intro g hg
      refine ⟨h hg, ?_⟩
      rw [← hV1]
      exact ⟨g, h hg, hfixθ g hg⟩
    · intro g hg
      refine ⟨?_, h hg⟩
      rw [← hV2]
      exact ⟨g, h hg, hfixθ g hg⟩
  set E₀ := E ⊓ c.range with hE₀
  set E₁ := E ⊓ semilinearAutGroup 3 F with hE₁
  have hEB : B.map c = E₀ := by rw [hB, Subgroup.map_comap_eq, inf_comm]
  have hcardB : Nat.card E₀ = Nat.card B := by
    rw [← hEB]
    exact Subgroup.card_map_of_injective hinj
  have hE₀E₁ : E₀ ≤ E₁ := inf_le_inf_left _ (by
    obtain ⟨hID, -⟩ := standard_outer_quotients (K := F) (n := 3)
    exact hID.trans linearAutGroup_le_semilinearAutGroup)
  have hc1 : Nat.card E = E₁.relIndex E * Nat.card E₁ := by
    have := Subgroup.relIndex_mul_card (H := E₁) (K := E)
    rw [inf_of_le_left inf_le_left] at this
    exact this.symm
  have hc2 : Nat.card E₁ = E₀.relIndex E₁ * Nat.card E₀ := by
    have := Subgroup.relIndex_mul_card (H := E₀) (K := E₁)
    rw [inf_of_le_left hE₀E₁] at this
    exact this.symm
  have hi₁ : E₁.relIndex E ≤ 2 := relIndex_inf_semilinear_le E
  have hi₂ : E₀.relIndex E₁ ≤ 2 := relIndex_inner_le E h2
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hB1 : B ≠ ⊥ := by
    intro h
    have h1 : Nat.card B = 1 := by rw [h, Subgroup.card_bot]
    have : Nat.card E ≤ 4 := by
      rw [hc1, hc2, hcardB, h1, mul_one]
      calc E₁.relIndex E * E₀.relIndex E₁ ≤ 2 * 2 := Nat.mul_le_mul hi₁ hi₂
        _ = 4 := by norm_num
    omega
  refine ⟨hBW, hB1, ?_⟩
  by_contra hno
  push Not at hno
  obtain ⟨θ₂, hθ₂E, hθ₂⟩ : ∃ θ₂ ∈ E, θ₂ ∉ semilinearAutGroup 3 F := by
    by_contra h
    push Not at h
    obtain ⟨u, hu, huW, -⟩ := exists_inner_V_of_le_semilinear hn hF E h2 hc hU h hcard
    exact huW (hBW hu)
  by_cases hE₁I : E₁ ≤ c.range
  ·
    have hE₁E₀ : E₁ = E₀ := le_antisymm (le_inf inf_le_left hE₁I) hE₀E₁
    have hcE₁ : Nat.card E₁ = Nat.card B := by rw [hE₁E₀, hcardB]
    have hEle : Nat.card E ≤ 2 * Nat.card B := by
      rw [hc1, hcE₁]
      exact Nat.mul_le_mul_right _ hi₁
    have hBW' : B = Wg := by
      refine Subgroup.eq_of_le_of_card_ge hBW ?_
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBW
      rw [card_Wg] at hk ⊢
      have hBpos : 0 < Nat.card B := Nat.card_pos
      have hk1 : k < 2 := by nlinarith
      interval_cases k <;> omega
    obtain ⟨g, hg, hne⟩ := hno θ₂ hθ₂E hθ₂
    exact hne (hfixE θ₂ hθ₂E g (hBW' ▸ hg))
  · obtain ⟨θ₁, hθ₁E₁, hθ₁I⟩ : ∃ θ₁ ∈ E₁, θ₁ ∉ c.range := by
      by_contra h
      push Not at h
      exact hE₁I h
    obtain ⟨hθ₁E, hθ₁s⟩ := Subgroup.mem_inf.mp hθ₁E₁
    have hθ₁D : θ₁ ∉ linearAutGroup 3 F := by
      intro hD'
      have : θ₁ ∈ E ⊓ linearAutGroup 3 F := ⟨hθ₁E, hD'⟩
      rw [inf_linear_eq_inf_inner E h2] at this
      exact hθ₁I this.2
    have hsq := card_sq_le_center hBW hθ₁s hθ₁D (hfixE θ₁ hθ₁E)
    have hEle : Nat.card E ≤ 4 * Nat.card B := by
      rw [hc1, hc2, hcardB]
      calc E₁.relIndex E * (E₀.relIndex E₁ * Nat.card B) ≤ 2 * (2 * Nat.card B) :=
            Nat.mul_le_mul hi₁ (Nat.mul_le_mul_right _ hi₂)
        _ = 4 * Nat.card B := by ring
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBW
    rw [card_Wg, hF] at hk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ⟨k, hk⟩
    have hm0 : m ≠ 0 := fun h => hB1 (Subgroup.eq_bot_of_card_eq B (by rw [hm, h, pow_zero]))
    rw [hm, hF, ← pow_mul] at hsq
    have h2m : m * 2 ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).mp hsq
    have hlt : 2 ^ n < 2 ^ (m + 2) := by
      calc 2 ^ n < Nat.card E := hF ▸ hcard
        _ ≤ 4 * 2 ^ m := hm ▸ hEle
        _ = 2 ^ (m + 2) := by ring
    have hnm : n < m + 2 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
    have hm1 : m = 1 := by omega
    have hn2 : n = 2 := by omega
    have hF4 : Nat.card F = 4 := by rw [hF, hn2]; norm_num
    have hB2' : Nat.card B = 2 := by rw [hm, hm1, pow_one]
    have h₁ : ¬ ∀ g ∈ (Wg : Subgroup (projectiveSL 3 F)), θ₁ g = g := by
      intro h
      have := card_sq_le_center le_rfl hθ₁s hθ₁D h
      rw [card_Wg, hF4] at this
      norm_num at this
    rcases fix_Wg_of_card_four hF4 hBW hB2' (hU θ₁ hθ₁E) (hU θ₂ hθ₂E) (hfixE θ₁ hθ₁E)
        (hfixE θ₂ hθ₂E) h₁ with h | h
    · obtain ⟨g, hg, hne⟩ := hno θ₂ hθ₂E hθ₂
      exact hne (h g hg)
    · have hmem : θ₁ * θ₂ ∉ semilinearAutGroup 3 F := fun hs => hθ₂ (by
        have := mul_mem (inv_mem hθ₁s) hs
        rwa [inv_mul_cancel_left] at this)
      obtain ⟨g, hg, hne⟩ := hno (θ₁ * θ₂) (mul_mem hθ₁E hθ₂E) hmem
      exact hne (h g hg)

end L3T

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
