module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCrossLin
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofHighWit

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8ModelProof

open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec21.Item223CensusResProof
open Matrix

variable {K K' : Type} [Field K] [Field K'] (ψ : K' ≃+* K) (n : ℕ)

theorem congr_fieldAut_slEquiv (σ : K' ≃+* K') :
    MulAut.congr (psOfSL (slEquiv ψ n)) (fieldAut n K' σ) =
      fieldAut n K (ψ.symm.trans (σ.trans ψ)) := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  simp only [MulAut.congr_apply, MulEquiv.trans_apply]
  rw [psOfSL_symm_proj, fieldAut_proj, psOfSL_proj, fieldAut_proj]
  congr 1

theorem congr_dualAut_slEquiv :
    MulAut.congr (psOfSL (slEquiv ψ n)) (dualAut n K') = dualAut n K := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  simp only [MulAut.congr_apply, MulEquiv.trans_apply]
  rw [psOfSL_symm_proj, dualAut_proj, psOfSL_proj, dualAut_proj]
  congr 1
  have hinv : (slEquiv ψ n) ((slEquiv ψ n).symm g)⁻¹ = g⁻¹ := by
    rw [map_inv, MulEquiv.apply_symm_apply]
  have htr : ∀ A : SpecialLinearGroup (Fin n) K', (slEquiv ψ n) A.transpose =
      ((slEquiv ψ n) A).transpose := fun A => by
    ext i j
    rfl
  rw [htr, hinv]

theorem hasKind_congr_slEquiv {τ : MulAut (projectiveSL n K')} {k : AutKind}
    (h : (stdPinnedPSL n K').HasKind τ k) :
    (stdPinnedPSL n K).HasKind (MulAut.congr (psOfSL (slEquiv ψ n)) τ) k := by
  set Φ := psOfSL (slEquiv ψ n) with hΦ
  have hne : ∀ {β : MulAut (projectiveSL n K')}, β ≠ 1 → MulAut.congr Φ β ≠ 1 := by
    intro β hβ h1
    exact hβ ((MulAut.congr Φ).injective (h1.trans (map_one _).symm))
  have hd : ∀ {d : MulAut (projectiveSL n K')}, d ∈ (stdPinnedPSL n K').inndiag →
      MulAut.congr Φ d ∈ (stdPinnedPSL n K).inndiag :=
    fun hd => congr_mem_linearAutGroup_slEquiv ψ n hd
  have hf : ∀ {φ : MulAut (projectiveSL n K')}, φ ∈ (stdPinnedPSL n K').field →
      MulAut.congr Φ φ ∈ (stdPinnedPSL n K).field := by
    rintro _ ⟨σ, rfl⟩
    exact ⟨ψ.symm.trans (σ.trans ψ), (congr_fieldAut_slEquiv ψ n σ).symm⟩
  have hg : ∀ {γ : MulAut (projectiveSL n K')}, γ ∈ (stdPinnedPSL n K').graph →
      MulAut.congr Φ γ ∈ (stdPinnedPSL n K).graph := by
    intro γ hγ
    rw [stdPinnedPSL_graph, Set.mem_singleton_iff] at hγ ⊢
    rw [hγ]
    exact congr_dualAut_slEquiv ψ n
  cases k with
  | inner => exact (isInnerAut_congr Φ τ).mpr h
  | diagonal => exact ⟨hd h.1, fun h' => h.2 ((isInnerAut_congr Φ τ).mp h')⟩
  | field =>
    obtain ⟨φ, hφ, hφ1, d, hdm, rfl⟩ := h
    exact ⟨_, hf hφ, hne hφ1, _, hd hdm, PinnedAut.congr_conj_mul Φ d φ⟩
  | graph =>
    obtain ⟨γ, hγ, hγ1, d, hdm, rfl⟩ := h
    exact ⟨_, hg hγ, hne hγ1, _, hd hdm, PinnedAut.congr_conj_mul Φ d γ⟩
  | graphField =>
    obtain ⟨γ, hγ, hγ1, φ, hφ, hφ1, d, hdm, rfl⟩ := h
    exact ⟨_, hg hγ, hne hγ1, _, hf hφ, hne hφ1, _, hd hdm, by
      rw [PinnedAut.congr_conj_mul, map_mul]⟩

include ψ in
theorem inducesKindPSL_of_ringEquiv {G : Type*} [Group G] [Finite G] {L : Subgroup G} {x : G}
    {k : AutKind} (h : InducesKindPSL n K' L x k) : InducesKindPSL n K L x k := by
  obtain ⟨e, hx, hk⟩ := h
  refine ⟨e.trans (psOfSL (slEquiv ψ n)), hx, ?_⟩
  rw [show inducedAutHom L (e.trans (psOfSL (slEquiv ψ n))) ⟨x, hx⟩ =
    MulAut.congr (psOfSL (slEquiv ψ n)) (inducedAutHom L e ⟨x, hx⟩) from congr_trans _ _ _]
  exact hasKind_congr_slEquiv ψ n hk

end CFSG.RankThree.PartTwo.Sec8.Item8ModelProof
