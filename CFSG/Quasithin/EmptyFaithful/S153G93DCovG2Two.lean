module

public import CFSG.Quasithin.EmptyFaithful.LRed7Zorn

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace CovG2

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.LRed7 CFSG.Open
open scoped Matrix

local notation "Amb" => quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)

section Act

variable {F : Type} [Field F] [CharP F 2]

theorem act_mul (g h : ↥(cayleyGroup F)) (w : Ix3 → F) :
    g2Act (g * h) w = g2Act g (g2Act h w) := by
  rw [map_mul]
  rfl

theorem act_one (w : Ix3 → F) : g2Act (1 : ↥(cayleyGroup F)) w = w := by
  rw [map_one]
  rfl

theorem act_inv_apply (g : ↥(cayleyGroup F)) (w : Ix3 → F) : g2Act g⁻¹ (g2Act g w) = w := by
  rw [← act_mul, inv_mul_cancel, act_one]

end Act

@[expose] def wordElem : List Bool → ↥(cayleyGroup (ZMod 2))
  | [] => 1
  | false :: ws => g2a * wordElem ws
  | true :: ws => g2b * wordElem ws

theorem g2b_pow_three :
    g2b ^ 3 = 1 := by
  apply cmat_injective
  rw [map_pow, cmat_g2b, map_one]
  decide +kernel

theorem act_a
    (w : Ix3 → ZMod 2) : g2Act g2a w = A6 *ᵥ w := by
  rw [g2Act_eq_mulVec, cmat_g2a]
  rfl

theorem act_b
    (w : Ix3 → ZMod 2) : g2Act g2b w = B6 *ᵥ w := by
  rw [g2Act_eq_mulVec, cmat_g2b]
  rfl

theorem act_b_w₀ :
    g2Act g2b w₀ = w₀ := by
  rw [act_b]
  apply code_inj
  rw [code_mulVec_B', code_w₀]
  decide +kernel

theorem code_e₁ : code (q6 (0 : ZMod 2) 1 0 0 0 0) = 2 := by
  decide +kernel

theorem exists_moved_b :
    ∃ w : Ix3 → ZMod 2, g2Act g2b w ≠ w := by
  refine ⟨q6 0 1 0 0 0 0, fun h => ?_⟩
  rw [act_b] at h
  have h1 := congrArg code h
  rw [code_mulVec_B', code_e₁] at h1
  revert h1
  decide +kernel

theorem wordElem_mem
    (ws : List Bool) :
    (wordElem ws : Amb) ∈ ⁅cayleyGroup (ZMod 2), cayleyGroup (ZMod 2)⁆ := by
  induction ws with
  | nil => exact Subgroup.one_mem _
  | cons b ws ih =>
    cases b
    · exact Subgroup.mul_mem _ g2a_mem ih
    · exact Subgroup.mul_mem _ g2b_mem ih

theorem code_act_wordElem
    (ws : List Bool) :
    code (g2Act (wordElem ws) w₀) = applyW ws := by
  induction ws with
  | nil =>
    rw [wordElem, act_one]
    exact code_w₀
  | cons b ws ih =>
    cases b
    · rw [wordElem, act_mul, act_a, code_mulVec_A', ih]
      simp [applyW]
    · rw [wordElem, act_mul, act_b, code_mulVec_B', ih]
      simp [applyW]

theorem exists_conj
    (g : ↥(cayleyGroup (ZMod 2)))
    (hg : (g : Amb) ∈ ⁅cayleyGroup (ZMod 2), cayleyGroup (ZMod 2)⁆) :
    ∃ x : ↥(cayleyGroup (ZMod 2)), (x : Amb) ∈ ⁅cayleyGroup (ZMod 2), cayleyGroup (ZMod 2)⁆ ∧
      x ^ 3 = 1 ∧ g2Act x (g2Act g w₀) = g2Act g w₀ ∧ ∃ w', g2Act x w' ≠ w' := by
  refine ⟨g * g2b * g⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg g2b_mem) (Subgroup.inv_mem _ hg)
  · rw [conj_pow, g2b_pow_three, mul_one, mul_inv_cancel]
  · rw [act_mul, act_mul, act_inv_apply, act_b_w₀]
  · obtain ⟨w, hw⟩ := exists_moved_b
    refine ⟨g2Act g w, fun h => hw ?_⟩
    rw [act_mul, act_mul, act_inv_apply] at h
    have h2 := congrArg (g2Act g⁻¹) h
    rwa [act_inv_apply, act_inv_apply] at h2

theorem exists_order_three_fix_two
    (w : Ix3 → ZMod 2) :
    ∃ x : ↥(cayleyGroup (ZMod 2)), (x : Amb) ∈ ⁅cayleyGroup (ZMod 2), cayleyGroup (ZMod 2)⁆ ∧
      x ^ 3 = 1 ∧ g2Act x w = w ∧ ∃ w', g2Act x w' ≠ w' := by
  by_cases hw : w = 0
  · obtain ⟨x, hx, h3, -, hne⟩ := exists_conj 1 (Subgroup.one_mem _)
    exact ⟨x, hx, h3, by rw [hw, map_zero], hne⟩
  · have hc0 : 0 < code w := by
      by_contra h
      have h0 : code w = 0 := by omega
      exact hw (code_inj (h0.trans code_zero.symm))
    have hspec := wordTable_spec ⟨code w, code_lt w⟩ hc0
    have hg : g2Act (wordElem (wordTable.getD (code w) [])) w₀ = w :=
      code_inj ((code_act_wordElem _).trans hspec)
    obtain ⟨x, hx, h3, hfix, hne⟩ :=
      exists_conj (wordElem (wordTable.getD (code w) [])) (wordElem_mem _)
    exact ⟨x, hx, h3, by rw [hg] at hfix; exact hfix, hne⟩

end CovG2

end S153G93D

end CFSG.Quasithin
