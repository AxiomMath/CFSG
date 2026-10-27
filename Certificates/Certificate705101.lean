module

public import CFSG.LargeExtraspecial.SL4ModClassSpec
public import Certificates.Data.SL4ModClassData
import Certificates.Kernel.SL4ModClass.Facts
public import CFSG.LargeExtraspecial.SL4ModEmbed

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace Certificates

open CertificateChecks

open CFSG.LargeExtraspecial.SL4Mod CFSG.LargeExtraspecial.SL4Mod.Native Matrix in
theorem certificate705101 :
    (∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V],
      Module.finrank (ZMod 2) V = 14 → ∀ ρ : SL4 →* (V ≃ₗ[ZMod 2] V), IsIrredGen ρ →
        ∃ e : V ≃ₗ[ZMod 2] (Fin 14 → ZMod 2), ∀ (s : Fin 6) (v : V),
          e (ρ (genN s.val) v) = refMat 14 ((classRefRows14[0]!)[s.val]!) *ᵥ e v) ∧
    (∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V],
      Module.finrank (ZMod 2) V = 20 → ∀ ρ : SL4 →* (V ≃ₗ[ZMod 2] V), IsIrredGen ρ →
        ∃ r : Fin 2, ∃ e : V ≃ₗ[ZMod 2] (Fin 20 → ZMod 2), ∀ (s : Fin 6) (v : V),
          e (ρ (genN s.val) v) = refMat 20 ((classRefRows20[r.val]!)[s.val]!) *ᵥ e v) := by
  refine ⟨fun _ _ _ _ hV _ hirr => ?_, fun _ _ _ _ hV _ hirr => ?_⟩
  · obtain ⟨r, hr, e, he⟩ := CFSG.LargeExtraspecial.SL4Mod.classify_of_classCertData
      (by norm_num) (by norm_num) KernelSL4ModClass.classCertData.1 hV hirr
    have hsize : CFSG.LargeExtraspecial.SL4Mod.Native.classRefRows14.size = 1 := rfl
    have hr0 : r = 0 := by omega
    subst hr0
    exact ⟨e, he⟩
  · obtain ⟨r, hr, e, he⟩ := CFSG.LargeExtraspecial.SL4Mod.classify_of_classCertData
      (by norm_num) (by norm_num) KernelSL4ModClass.classCertData.2 hV hirr
    have hsize : CFSG.LargeExtraspecial.SL4Mod.Native.classRefRows20.size = 2 := rfl
    exact ⟨⟨r, by omega⟩, e, he⟩

end Certificates
