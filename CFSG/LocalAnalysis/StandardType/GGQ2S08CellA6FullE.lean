module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TestCertFive
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellA7Full

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

variable {G : Type} [Group G] {Bs J : Subgroup G}

variable [Finite G] {L : Subgroup G} {x : G}

theorem ggQ2s08_cell_of_test_P (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) {B D : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) (M : GGQ2LDatum 3 Bs L x) {n : ℕ}
    (κ : M.V ≃ₗ[ZMod 3] Vn n) {x₀ : Vn n} (hκx : κ M.xV = x₀)
    {W : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} (hW : (ggAutomizer L Bs).map (ggQ2CellLin M κ) = W)
    (P : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n) → (Vn n ≃ₗ[ZMod 3] Vn n) → Prop)
    (htest : ∀ A Mg : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n), TestHyp W x₀ A Mg →
      ∀ r ∈ Mg, IsRefl r → ¬ FixesLine x₀ r →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine x₀ t → P Mg t → t ∈ Mg)
    (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ) (hRefl : GGIsReflection 3 φ)
    (hPφ : P ((ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs).map
      (ggQ2CellLin M κ)) (ggQ2CellLin M κ φ)) :
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
  obtain ⟨φ', hφ'M, hφ'⟩ := htest _ _ hH _ ⟨ρ, hρM, rfl⟩ (ggQ2Cell_isRefl M κ hρR)
    (hmoves ρ (ggQ2Cell_not_mem_zpowers_of_movesLine M.hx hρx)) _ ⟨φ, hφA, rfl⟩
    (ggQ2Cell_isRefl M κ hRefl) (hmoves φ hline) hPφ
  obtain rfl := ggQ2CellLin_injective M κ hφ'
  exact ggQ2Cell_normalizes_of_mem hΓ M.hx hInd hφ'M

theorem ggQ2s08_cellE_twA6_of_coords (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) {B D : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) (M : GGQ2LDatum 3 Bs L x)
    (κ : M.V ≃ₗ[ZMod 3] Vn 7) (hκx : κ M.xV = oneN 7)
    (hW : (ggAutomizer L Bs).map (ggQ2CellLin M κ) = Subgroup.closure (Set.range a7fS))
    (hJcen : ∃ S : Finset (Fin 7), 5 ≤ S.card ∧ ∀ b : ↥Bs,
      (b : G) ∈ Subgroup.centralizer (J : Set G) →
        ∀ a ∈ S, ∀ a' ∈ S, κ (M.model (Additive.ofMul b)) a = κ (M.model (Additive.ofMul b)) a')
    (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ) (hRefl : GGIsReflection 3 φ)
    (hE : GGQ2EForm Bs J φ) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  refine ggQ2s08_cell_of_test_P hLB hP hΓi hTBN hS hI1 hCav M κ hκx hW (fun _ => a7fCen)
    (fun A Mg hT r hr hrR hrx t ht htR htx hPt => a7f_test_cen A Mg hT r hr hrR hrx t ht htR htx
      hPt) g φ hInd hRefl ?_
  obtain ⟨S, hS5, hSJ⟩ := hJcen
  refine ⟨S, hS5, fun v a ha a' ha' => ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, κ (M.model (Additive.ofMul b)) = v :=
    ⟨Additive.toMul (M.model.symm (κ.symm v)), by
      rw [ofMul_toMul, AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩
  have hdisp : ggQ2CellLin M κ φ (κ (M.model (Additive.ofMul b))) -
      κ (M.model (Additive.ofMul b)) = κ (M.model (Additive.ofMul (b⁻¹ * φ b))) := by
    rw [ggQ2CellLin_apply, LinearEquiv.symm_apply_apply, ggLin_apply_ofMul, ofMul_mul, ofMul_inv,
      map_add, map_neg, neg_add_eq_sub, map_sub]
    rfl
  rw [hdisp]
  exact hSJ _ (hE.1 b) a ha a' ha'

end CFSG.StandardType

end
