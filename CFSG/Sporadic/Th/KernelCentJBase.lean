
module

public import CFSG.Sporadic.Th.KernelCent
public import CFSG.Sporadic.Th.KernelOrderBase
public import CFSG.Certificates.Kernel.ThCent.WitSoundBase
public import CFSG.Certificates.Kernel.Th.Spec.FwdExtBase
public import CFSG.Certificates.Kernel.Th.SoundnessGenBase
import CFSG.Certificates.Kernel.Th.Spec.Dce
import CFSG.Certificates.Kernel.Th.Spec.DceHsw
public import CFSG.Certificates.Kernel.Th.SoundnessGen
public import CFSG.Sporadic.Th.LocalBase
public import CFSG.Sporadic.ThSchreier.AutAssembly

@[expose] public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.Th CFSG.KC.Th CFSG.KC.ThCent CFSG.KC.Th.Spec.DceStr
  CFSG.KC.Th.Spec.Dce CFSG.KC.Th.Gen CFSG.KC.Th.Spec TauCeti Pointwise

theorem entN_eq_enT' : CFSG.KC.Th.Soundness.entN = enT := by
  have hw : ∀ w : List (ℕ × Bool), CFSG.KC.Th.Soundness.wordNatN w = wdN w := by
    intro w
    induction w with
    | nil => rfl
    | cons l w ih => simp only [CFSG.KC.Th.Soundness.wordNatN, wdN, ih,
        CFSG.KC.Th.Soundness.codeN, cdL]
  funext w
  simp only [CFSG.KC.Th.Soundness.entN, enT, hw]

theorem hsw_th : SporadicName.Th.presentation.generatorCount = 8 ∧
    (∀ r ∈ SporadicName.Th.presentation.relatorLetters, r.length < 1024) ∧
    SporadicName.Th.presentation.relatorLetters.map enT = CFSG.KC.Th.Hsw.list := by
  obtain ⟨h1, h2, h3⟩ := CFSG.KC.Th.Soundness.isHsw_th
  rw [entN_eq_enT'] at h3
  exact ⟨h1, h2, h3⟩

end CFSG.Sporadic.Th.Kernel

end
