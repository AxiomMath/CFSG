module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

theorem ggQ2s08_cell_of_test_Q {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) {B D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) (M : GGQ2LDatum 3 Bs L x) {n : ℕ}
    (κ : M.V ≃ₗ[ZMod 3] Vn n) {x₀ : Vn n} (hκx : κ M.xV = x₀)
    {W : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} (hW : (ggAutomizer L Bs).map (ggQ2CellLin M κ) = W)
    (P : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n) → Prop)
    (hPA : P ((ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ)))
    (Q : (Vn n ≃ₗ[ZMod 3] Vn n) → (Vn n ≃ₗ[ZMod 3] Vn n) → Prop)
    (htest : ∀ A Mg : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n), TestHyp W x₀ A Mg → P A →
      ∀ r ∈ Mg, IsRefl r → ¬ FixesLine x₀ r →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine x₀ t → t ∈ Mg ∨ Q r t)
    (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ) (hRefl : GGIsReflection 3 φ)
    (hQ : ∀ r ∈ (ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs).map
        (ggQ2CellLin M κ), IsRefl r → ¬ FixesLine x₀ r → Q r (ggQ2CellLin M κ φ) →
        g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G)) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  classical
  have hΓ : GGQ2GammaX 3 B Bs x L D J := hΓi hS rfl hI1 hCav
  have hAJ : ggAutomizer J Bs ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hCav
    exact absurd (Nat.le_of_dvd one_pos hCav) (by norm_num)
  have hH := ggQ2Cell_hyp hLB hP hS hΓ hAJ M κ hκx hW
  by_cases hline : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs)
  · refine hΓ g hInd.1 ?_
    have h1 := hInd.2 ⟨x, M.hx⟩
    rw [← h1]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hline
    rw [← hm]
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simp⟩
  obtain ⟨ρ, hρM, hρR, hρx⟩ := ggQ2_exists_movesLine_refl_M hTBN hS hI1
  have hmoves : ∀ ψ : MulAut ↥Bs, ψ ⟨x, M.hx⟩ ∉ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) →
      ¬ FixesLine x₀ (ggQ2CellLin M κ ψ) := fun ψ hψ h =>
    hψ (ggQ2Cell_mem_zpowers_of_fixesLine M κ hκx h)
  have hφA : φ ∈ ggAutomizer ⊤ Bs :=
    mem_ggAutomizer_iff.mpr ⟨g, Subgroup.mem_top _, hInd.1, hInd.2⟩
  have hρmoves : ¬ FixesLine x₀ (ggQ2CellLin M κ ρ) :=
    hmoves ρ (ggQ2Cell_not_mem_zpowers_of_movesLine M.hx hρx)
  rcases htest _ _ hH hPA (ggQ2CellLin M κ ρ) ⟨ρ, hρM, rfl⟩ (ggQ2Cell_isRefl M κ hρR)
      hρmoves (ggQ2CellLin M κ φ) ⟨φ, hφA, rfl⟩ (ggQ2Cell_isRefl M κ hRefl)
      (hmoves φ hline) with hmem | hQrt
  · obtain ⟨φ', hφ'M, hφ'⟩ := hmem
    obtain rfl := ggQ2CellLin_injective M κ hφ'
    exact ggQ2Cell_normalizes_of_mem hΓ M.hx hInd hφ'M
  · exact hQ (ggQ2CellLin M κ ρ) ⟨ρ, hρM, rfl⟩ (ggQ2Cell_isRefl M κ hρR) hρmoves hQrt

end CFSG.StandardType

end
