module

public import CFSG.LocalAnalysis.StandardType.GGSmallD2Ctx
public import CFSG.LocalAnalysis.StandardType.GGSmallDepDefs
import CFSG.LocalAnalysis.StandardType.GGSmallD2Rows
import CFSG.LocalAnalysis.StandardType.GGSmallD2Orth
import CFSG.LocalAnalysis.StandardType.GGSmallD2Weyl
import CFSG.LocalAnalysis.StandardType.GGSmallD2Restrict

public section

namespace CFSG.StandardType

namespace GGSmallD2Ctx

variable {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {A : Subgroup (V ≃ₗ[ZMod p] V)} {T : Submodule (ZMod p) V}
  {AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)}

theorem false
    (X : GGSmallD2Ctx p N A T AT) (hUse : ZS.UseInput)
    (hcell : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7) ∨ (p = 5 ∧ N = 10)) : False := by
  cases X.family hUse with
  | weyl hw => exact X.false_of_linWeyl hcell hw
  | slpm hsl => exact X.false_of_slpm hsl
  | orth Q _ hiso => exact X.false_of_orth hiso
  | orthClass Q c hQ hc hcl => exact X.false_of_orthClass hcell hQ hc hcl
  | @gmmn n f i₀ i₁ ζ m _ _ _ hQ => exact X.false_of_gmmn f i₀ i₁ ζ hQ
  | @g2mmn n f i₀ i₁ ζ m _ _ _ hQ => exact X.false_of_g2mmn f i₀ i₁ ζ hQ
  | exc k _ _ _ hcen _ _ _ => exact X.false_of_exc k hcen
  | h4 _ _ _ hneg _ _ => exact X.false_of_neg_mem hneg

end GGSmallD2Ctx

theorem ggSmallD2Input_of_use
    (hUse : ZS.UseInput) : GGSmallD2Input := by
  intro p N _ hcell
  have hN : 5 ≤ N := by
    rcases hcell with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  refine ⟨?_, ?_⟩
  · intro V _ _ _ h α x hp2 hdim F r hr ra ha αa hra hαa hjoin hw hnt hcard hnH
    obtain ⟨T, AT, X⟩ :=
      ggSmallD2Ctx_of_caseI hp2 hN hdim F r hr ra ha αa hra hαa hjoin hw hnt hcard hnH
    exact X.false hUse hcell
  · intro V _ _ _ h α x hp2 hdim F r hr ra ha αa hra hαa hw hnt hcard hH
    obtain ⟨T, AT, X⟩ :=
      ggSmallD2Ctx_of_caseII hp2 hN hdim F r hr ra ha αa hra hαa hw hnt hcard hH
    exact X.false hUse hcell

end CFSG.StandardType

end
