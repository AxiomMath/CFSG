module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.OmegaSmallTransport
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SUForms
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinMinus

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem

namespace CFSG.StandardType.LieKnownR2.POmega

theorem ggRootItemTwo_pomegaMinus_three
    {f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X] [Finite X]
    (φ : (ggU .POmegaMinus 3 f).K →* X)
    (hker : φ.ker ≤ Subgroup.center (ggU .POmegaMinus 3 f).K)
    {β : Fin (ggU .POmegaMinus 3 f).D.rank → ℤ} (hβ : β ∈ (ggU .POmegaMinus 3 f).D.roots)
    (hl : GGLongRoot (ggU .POmegaMinus 3 f).D β) (u : (ggU .POmegaMinus 3 f).K) :
    GGRootInnerAt φ.range (ggRootSub (ggU .POmegaMinus 3 f).D φ β u) ∧
      GGRootNoCentralAt φ.range (ggRootSub (ggU .POmegaMinus 3 f).D φ β u) := by
  obtain ⟨e, he⟩ := CFSG.StandardType.RCKRP.irgIsoCompat_omegaMinus_three (g := f) hf
  obtain ⟨γ, ⟨hγ, hγgood⟩, w, h1, -⟩ := he β hβ hl
  have hγl : GGLongRoot (ggU .PSU 4 f).D γ := by
    rcases hγgood with h | ⟨h, -⟩
    · exact h
    · exfalso
      rcases h with h | h
      · exact absurd h.1 (by decide)
      · exact absurd h (by decide)
  rw [omegaSmall_ggRootSub_transport e φ w h1 u, ← omegaSmall_range_eq e φ]
  have hker' := omegaSmall_ker_le_center e φ hker
  exact ⟨PSU.ggRootInnerAt_ggU_psu (n := 4) (by norm_num) (by omega)
      (φ.comp e.symm.toMonoidHom) hker' hγ (Or.inl hγl) (e u * w),
    PSU.ggRootNoCentralAt_ggU_psu (n := 4) (by norm_num) (by omega)
      (φ.comp e.symm.toMonoidHom) hker' hγ (Or.inl hγl) (e u * w)⟩

end CFSG.StandardType.LieKnownR2.POmega

end
