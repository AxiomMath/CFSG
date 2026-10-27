module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.OmegaSmallTransport
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLPos
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinPlus

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem

namespace CFSG.StandardType.LieKnownR2.POmega

theorem ggRootItemTwo_pomegaPlus_three
    {f : ℕ} (hf : 2 ≤ f) {X : Type} [Group X] [Finite X]
    (φ : (ggU .POmegaPlus 3 f).K →* X)
    (hker : φ.ker ≤ Subgroup.center (ggU .POmegaPlus 3 f).K)
    {β : Fin (ggU .POmegaPlus 3 f).D.rank → ℤ} (hβ : β ∈ (ggU .POmegaPlus 3 f).D.roots)
    (hl : GGLongRoot (ggU .POmegaPlus 3 f).D β) (u : (ggU .POmegaPlus 3 f).K) :
    GGRootInnerAt φ.range (ggRootSub (ggU .POmegaPlus 3 f).D φ β u) ∧
      GGRootNoCentralAt φ.range (ggRootSub (ggU .POmegaPlus 3 f).D φ β u) := by
  obtain ⟨e, he⟩ := CFSG.StandardType.RCKRP.irgIsoCompat_omegaPlus_three (g := f) (by omega)
  obtain ⟨γ, ⟨hγ, -⟩, w, h1, -⟩ := he β hβ hl
  rw [omegaSmall_ggRootSub_transport e φ w h1 u, ← omegaSmall_range_eq e φ]
  exact PSL.itemTwo_ggU_psl (k := 3) (Or.inr (Or.inl ⟨hf, le_refl 3⟩))
    (φ.comp e.symm.toMonoidHom) (omegaSmall_ker_le_center e φ hker) hγ (e u * w) rfl

end CFSG.StandardType.LieKnownR2.POmega

end
