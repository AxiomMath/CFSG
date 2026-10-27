module

public import CFSG.Quasithin.Vol2.Ch6H11Main
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatOm4mA.HermCoords
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatOm4mA.Basic

public section

noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA

open CFSG.Quasithin
open CFSG.Quasithin.JonesParshall (sig)
open CFSG.Quasithin.H13.H11M (VH UH Ws SigInv)
open CFSG.Quasithin.H13.H11P (Uu uu mem_Uu)

variable {F : Type} [Field F] [CharP F 2] {a : ℕ} (hσ : SigInv a F)

theorem exists_witness_inner [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    {A : Subgroup (MulAut (VH a F))} (hAU : A ≤ UH hσ) (hA1 : A ≠ ⊥) :
    ∃ B : Subgroup (MulAut (VH a F)), B ≤ A ∧ E3.mQuot A B ≤ a ∧ fixV B ≠ fixV A := by
  obtain ⟨s₀, hs₀, hs₀0⟩ := exists_ne_zero_mem_Ws hσ hAU hA1
  by_cases hcol : ∀ s ∈ Ws hσ A, s * sig a s₀ = sig a s * s₀
  · refine ⟨⊥, bot_le, mQuot_bot_le_of_card_le A ?_, fixV_bot_ne_of_ne_bot hA1⟩
    exact card_le_of_collinear hσ ha hF hAU hs₀0 hcol
  · push Not at hcol
    obtain ⟨s₁, hs₁, hne⟩ := hcol
    set y : F := (sig a s₀)⁻¹ with hy
    have hS : ∀ x ∈ A, x (zy hσ y) ∈ zyCoset a y := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp (hAU hx)
      obtain ⟨s, rfl⟩ := mem_Uu.mp hg
      exact rhoH_uu_zy_mem_zyCoset hσ s y
    obtain ⟨B, hBA, hmB, hvB⟩ :=
      exists_le_mQuot_le_of_orbit_subset A (zy hσ y) (zyCoset a y) hS (card_zyCoset_le ha hF y)
    have ht : s₁ * sig a y + sig a s₁ * y ≠ 0 := by
      rw [hy]
      exact (trace_term_inv_eq_zero_iff hσ hs₀0).not.mpr hne
    exact ⟨B, hBA, hmB, fun h => (zy_not_mem_fixV hσ hs₁ ht) (h ▸ hvB)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA

end
