module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Diag2
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Diag3
public import CFSG.LocalAnalysis.WeakClosure81.W183K3AlphaQ
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Diag

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt)
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ A : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem br3_false_of_diagonal (hfin : FinG3) (h : Assumption131 Y Γ VA i)
    (hVfix : ∀ B ∈ Γ, VA B ≤ fixSub B) (htwo : Br3TwoComp Y T L₁ L₂)
    (hshape₁ : IsL3 (↥L₁ ⧸ Subgroup.center ↥L₁) 2 ∨ IsAlt (↥L₁ ⧸ Subgroup.center ↥L₁) 6)
    (hshape₂ : IsL3 (↥L₂ ⧸ Subgroup.center ↥L₂) 2 ∨ IsAlt (↥L₂ ⧸ Subgroup.center ↥L₂) 6)
    (hA : A ∈ Γ) (hr : mRank A ≤ i) (hcard : Nat.card ↥A = 4)
    (hAn₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hAn₂ : A ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)))
    (hC₁ : A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥)
    (hC₂ : A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥) : False := by
  classical
  have hel : IsElemAbelian 2 A := h.isElemAb A hA
  have hAY : A ≤ Y := h.le_G A hA
  have hTI : IsTISub ↥Y (A.subgroupOf Y) := h.isTISub_member hA hr
  have key : ∀ {Lj Lk : Subgroup (LGL 2 V)}, Br3TwoComp Y T Lj Lk →
      A ≤ Subgroup.normalizer (Lj : Set (LGL 2 V)) →
      A ≤ Subgroup.normalizer (Lk : Set (LGL 2 V)) →
      A ⊓ Subgroup.centralizer (Lj : Set (LGL 2 V)) = ⊥ →
      A ⊓ Subgroup.centralizer (Lk : Set (LGL 2 V)) = ⊥ →
      (IsL3 (↥Lj ⧸ Subgroup.center ↥Lj) 2 ∨ IsAlt (↥Lj ⧸ Subgroup.center ↥Lj) 6) →
      alphaA Y Lj A ≤ alphaL Y Lj ∧ ∃ nb ∈ alphaL Y Lj,
        (∀ x ∈ alphaA Y Lj A, nb * x * nb⁻¹ ∈ alphaA Y Lj A) ∧
        ∀ x ∈ alphaA Y Lj A, x ≠ 1 → nb * x * nb⁻¹ ≠ x := by
    intro Lj Lk htwo' hAnj hAnk hCj hCk hsh
    haveI : Finite (alphaQuot Y Lj) := w183_alpha_finite Y Lj
    obtain ⟨hN, hC⟩ := w183k3_alpha_normal_cent htwo'.quasi₁ htwo'.le₁
    obtain ⟨e⟩ := w183k3_alpha_shape htwo'.le₁
    obtain ⟨hcard', hel'⟩ := w183_alpha_card_elem hAY hAnj hCj hcard hel
    have hti := w183k3_diag_ti htwo' hAY hel.isPGroup hAnj hAnk hCk hTI
    have hfin' := hfin (alphaQuot Y Lj) (alphaL Y Lj) hN hC (alphaA Y Lj A) hcard' hel' hti
    rcases hsh with h3 | h6
    · exact hfin'.1 (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h3)))
    · obtain ⟨e'⟩ := h6
      exact (hfin'.2 (Or.inr ⟨e.symm.trans e'⟩)).elim
  obtain ⟨hin₁, hn⟩ := key htwo hAn₁ hAn₂ hC₁ hC₂ hshape₁
  obtain ⟨hin₂, -⟩ := key htwo.symm hAn₂ hAn₁ hC₂ hC₁ hshape₂
  obtain ⟨X₁, X₂, φ, hX₁, hX₂, hX₁c, hX₁sq, hD₀eq, n, hnL, hnX, hfpf⟩ :=
    w183k3_diag_decomp htwo hAY hel hcard hAn₁ hAn₂ hC₁ hC₂ hin₁ hin₂ hn
  exact h.false_of_diagonal_member_quasi hVfix htwo.quasi₁ htwo.quasi₂ htwo.odd₁ htwo.odd₂
    htwo.le₁ htwo.comm hX₁ hX₂ hX₁c hX₁sq φ hA hr hD₀eq hnL hnX hfpf

end CFSG.LocalAnalysis.WeakClosure81

end
