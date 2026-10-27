module

public import CFSG.Quasithin.Background.HL3WrV5

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr

theorem rho_c3_one_mem_stabE : rho (c3, 1) ∈ stabE :=
  mem_stabE_iff.2 ⟨img_le_norm (rho_mem_img _), rho_fix_E00 c3_mem_P1 P1.one_mem⟩

theorem rho_one_c3_mem_stabE : rho (1, c3) ∈ stabE :=
  mem_stabE_iff.2 ⟨img_le_norm (rho_mem_img _), rho_fix_E00 P1.one_mem c3_mem_P1⟩

theorem rho_u0_one_mem_stabE : rho (u0, 1) ∈ stabE :=
  mem_stabE_iff.2 ⟨img_le_norm (rho_mem_img _), rho_fix_E00 (U3_le_P1 u0_mem_U3) P1.one_mem⟩

theorem tau_mem_stabE : tau ∈ stabE :=
  mem_stabE_iff.2 ⟨tau_mem_norm, tau_eW_diag 0⟩

theorem chief_Z00_V5 :
    Z00 < V5 ∧ (∀ y ∈ stabE, ∀ u ∈ Z00, y u ∈ Z00) ∧ (∀ y ∈ stabE, ∀ u ∈ V5, y u ∈ V5) ∧
      ∀ W : Subgroup WMod, Z00 ≤ W → W ≤ V5 → (∀ y ∈ stabE, ∀ u ∈ W, y u ∈ W) →
        W = Z00 ∨ W = V5 := by
  refine ⟨?_, fun y hy u hu => map_mem_Z00_of_mem_stabE hy hu,
    fun y hy u hu => map_mem_V5_of_mem_stabE hy hu, ?_⟩
  · refine lt_of_le_of_ne Z00_le_V5 fun h => ?_
    have h1 : eW 0 1 ∈ V5 := eW_mem_V5_row 1
    rw [← h] at h1
    have h2 := mem_Z00_iff.1 h1
    revert h2
    decide
  · intro W hZW hW5 hinv
    by_cases hW : W ≤ Z00
    · exact Or.inl (le_antisymm hW hZW)
    · refine Or.inr (le_antisymm hW5 ?_)
      exact V5_le_of_irred (hZW (Subgroup.mem_zpowers _)) hW5 hW
        (fun X hX => hinv _ rho_c3_one_mem_stabE X hX)
        (fun X hX => hinv _ rho_one_c3_mem_stabE X hX) tau_mem_stabE tau_not_mem_img
        (fun X hX => hinv _ tau_mem_stabE X hX)

theorem chief_V5_top :
    V5 < ⊤ ∧ (∀ y ∈ stabE, ∀ u ∈ V5, y u ∈ V5) ∧ (∀ y ∈ stabE, ∀ u ∈ (⊤ : Subgroup WMod), y u ∈ (⊤ : Subgroup WMod)) ∧
      ∀ W : Subgroup WMod, V5 ≤ W → W ≤ ⊤ → (∀ y ∈ stabE, ∀ u ∈ W, y u ∈ W) →
        W = V5 ∨ W = ⊤ := by
  refine ⟨?_, fun y hy u hu => map_mem_V5_of_mem_stabE hy hu,
    fun y _ u _ => Subgroup.mem_top _, ?_⟩
  · refine lt_top_iff_ne_top.2 fun h => ?_
    have h1 : eW 1 1 ∈ V5 := by rw [h]; exact Subgroup.mem_top _
    have h2 := (mem_V5.1 h1).1
    revert h2
    decide
  · intro W h5W _ hinv
    by_cases hW : W ≤ V5
    · exact Or.inl (le_antisymm hW h5W)
    · exact Or.inr (eq_top_of_irred h5W hW
        (fun X hX => hinv _ rho_c3_one_mem_stabE X hX)
        (fun X hX => hinv _ rho_one_c3_mem_stabE X hX)
        (fun X hX => hinv _ rho_u0_one_mem_stabE X hX))

end CFSG.Quasithin.RonanH49
