module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3AlphaQ
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Shape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ A : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem w183k3_alpha_false_A6 (hfin : FinA6) (h : Assumption131 Y Γ VA i)
    (htwo : Br3TwoComp Y T L₁ L₂) (hA : A ∈ Γ) (hr : mRank A ≤ i) (hcard : Nat.card ↥A = 4)
    (hn₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hker₁ : A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥)
    (hcent₂ : A ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hshape : IsAlt (↥L₁ ⧸ Subgroup.center ↥L₁) 6)
    (hτ : ∃ τ ∈ Y, ActsOnDynkinMod (quasiCentre L₁) L₁ τ) : False := by
  classical
  haveI : Finite (alphaQuot Y L₁) := w183_alpha_finite Y L₁
  obtain ⟨hN, hC⟩ := w183k3_alpha_normal_cent htwo.quasi₁ htwo.le₁
  obtain ⟨e⟩ := w183k3_alpha_shape htwo.le₁
  obtain ⟨e'⟩ := hshape
  have hshape' : IsAlt ↥(alphaL Y L₁) 6 := ⟨e.symm.trans e'⟩
  have hAY : A ≤ Y := h.le_G A hA
  have hel : IsElemAbelian 2 A := h.isElemAb A hA
  obtain ⟨hcard', hel'⟩ := w183_alpha_card_elem hAY hn₁ hker₁ hcard hel
  have hTI' : IsTISub (alphaQuot Y L₁) (alphaA Y L₁ A) :=
    w183k3_alpha_ti htwo hAY hel.isPGroup hn₁ hcent₂ (h.isTISub_member hA hr)
  obtain ⟨τ, hτY, hτd⟩ := hτ
  obtain ⟨τ', hτ''⟩ := w183k3_alpha_dynkin htwo.le₁ hτY hτd
  exact hfin (alphaQuot Y L₁) (alphaL Y L₁) hN hshape' hC ⟨τ', hτ''⟩ (alphaA Y L₁ A)
    hcard' hel' hTI'

end CFSG.LocalAnalysis.WeakClosure81

end
