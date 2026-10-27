module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixSylow
import CFSG.LocalAnalysis.StandardType.FS81.N7FixDentGrp
import CFSG.LocalAnalysis.StandardType.FS81.N7FixDentPerm
import CFSG.LocalAnalysis.StandardType.FS81.N7FixDentNorm

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

namespace N7Setup

variable {X : Type} [Group X] [Finite X] (S : N7Setup X)

theorem stronglyClosed_centralizer {τ : X} (hτ : S.ρ τ ∈ E6set) :
    ∀ a ∈ S.F1, ∀ d : X, d * τ = τ * d → d⁻¹ * a * d ∈ S.H → d⁻¹ * a * d ∈ S.F1 := by
  intro a ha d hd hH
  obtain ⟨S0, h0, hc, hρ⟩ := hτ
  have hdD : d ∈ S.dentD S0 := (S.mem_dentD_iff_comm hρ).2 hd
  refine S.mem_F1_of_comm_dentF2 h0 hc hH ?_
  intro f hf
  have hf' : d * f * d⁻¹ ∈ S.dentF2 S0 := S.dentF2_conj_mem h0 hc hdD hf
  have hf'F1 : d * f * d⁻¹ ∈ S.F1 := (Subgroup.mem_inf.1 hf').1
  have hcomm : a * (d * f * d⁻¹) = (d * f * d⁻¹) * a := S.F1_comm ha hf'F1
  calc (d⁻¹ * a * d) * f = d⁻¹ * (a * (d * f * d⁻¹)) * d := by group
    _ = d⁻¹ * ((d * f * d⁻¹) * a) * d := by rw [hcomm]
    _ = f * (d⁻¹ * a * d) := by group

end N7Setup

end CFSG.StandardType.FrameRoute.FS81

end
