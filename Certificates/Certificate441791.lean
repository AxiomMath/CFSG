module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ADef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Rules
import Certificates.Kernel.FzZ8.FusionG
import CFSG.Certificates.Kernel.FzZ8.Enum
import CFSG.Certificates.Kernel.FzZ8.Relabel

public section

namespace Certificates

open Certificates.FzR10A CFSG.KC.FzZ8

theorem certificate441791 : ∀ Mt Ms Ml : FzR10A.Mat, CFSG.OddStandard.SmallF3.FritzII.FzR10AMatLt Mt →
    CFSG.OddStandard.SmallF3.FritzII.FzR10AMatLt Ms →
    CFSG.OddStandard.SmallF3.FritzII.FzR10AMatLt Ml → FzR10A.candT Mt = true →
    FzR10A.candS Mt Ms = true → FzR10A.candL Mt Ml = true → Ms.mul Ml = Ml.mul Ms →
    ¬ ∃ θ : ℕ → Prop, CFSG.OddStandard.SmallF3.FritzII.FzRules (FzR10A.parOfA Mt Ms Ml) θ :=
  fun _ _ _ hMt hMs hMl hT hS hL hc => by
    obtain ⟨rfl, hs, hl⟩ := enumA hMt hMs hMl hT hS hL (beq_iff_eq.mpr hc)
    rcases hs with rfl | rfl
    · exact relabel_lsA (Or.inl rfl) hl fusion_r3
    · exact relabel_lsA (Or.inr rfl) hl fusion_r7

end Certificates
