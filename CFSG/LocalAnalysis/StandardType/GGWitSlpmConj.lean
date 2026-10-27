module

public import CFSG.LocalAnalysis.StandardType.GGWitSlpm

import CFSG.LocalAnalysis.StandardType.GGWitSlpmConjAux

public section

namespace CFSG.StandardType.ZS

open Subgroup

theorem slpm_conj {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] (hd : 3 ≤ Module.finrank (ZMod p) U)
    (a b : U) (α β : U →ₗ[ZMod p] ZMod p) (hα : α a = 2) (hβ : β b = 2) :
    ∃ g : U ≃ₗ[ZMod p] U, LinearEquiv.det g = 1 ∧
      g * slpmRefl a α hα * g⁻¹ = slpmRefl b β hβ := by
  obtain ⟨g, hgdet, hgconj⟩ :=
    wSlpmC_isRefl_conj hp2 hd (slpmRefl a α hα) (slpmRefl b β hβ)
      (slpmRefl_isRefl_det hp2 a α hα).1 (slpmRefl_isRefl_det hp2 b β hβ).1
  exact ⟨g, hgdet, hgconj⟩

end CFSG.StandardType.ZS

end
