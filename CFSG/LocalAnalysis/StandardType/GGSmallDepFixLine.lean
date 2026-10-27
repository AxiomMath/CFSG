module

public import CFSG.LocalAnalysis.StandardType.GGSmallDepRowWeyl
public import CFSG.LocalAnalysis.StandardType.GGSmallDepRowOrth
public import CFSG.LocalAnalysis.StandardType.GGSmallDepDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggSmallDepFixLineAt_of_use
    (hUse : ZS.UseInput) (p N : ℕ)
    [Fact p.Prime]
    (hcell : (p = 5 ∧ N = 5) ∨ (p = 3 ∧ N = 6) ∨ (p = 7 ∧ N = 7) ∨ (p = 5 ∧ N = 10)) :
    GGSmallDepFixLineAt p N := by
  intro V _ _ h α r T s x hlin hdep hstab hweyl
  by_contra hcon
  have htwo : 2 ≤ Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) := by omega
  have hN : 5 ≤ N := by
    rcases hcell with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hlin9 : GGNineLinHyp p N h α r s x :=
    ⟨hlin.p_ne_two, hN, hlin.p_dvd, hlin.dim_le, hlin.pair, hlin.refl_form, hlin.finT,
      hlin.s_refl, hlin.conn, hlin.x_ne, hlin.fix_s, hlin.x_not_fix, hlin.no_transv⟩
  have X : GGNineDepCtx h α r s x := ggNineDepCtx_of_case ⟨hlin9, hdep, hstab, htwo, hweyl⟩
  cases X.family hUse with
  | weyl hw => exact X.false_of_linWeyl hcell hw
  | slpm hsl => exact X.false_of_slpm hsl
  | orth Q hQ hiso => exact X.false_of_orth hcell hQ hiso
  | orthClass Q c hQ hc hcl => exact X.false_of_orthClass hcell hQ hc hcl
  | @gmmn n f i₀ i₁ ζ m _ _ _ hQ => exact X.false_of_gmmn f i₀ i₁ ζ hQ
  | @g2mmn n f i₀ i₁ ζ m _ _ _ hQ => exact X.false_of_g2mmn f i₀ i₁ ζ hQ
  | exc k hk hdeg hord hcen _ _ _ => exact X.false_of_exc hcell k hk hdeg hord hcen
  | h4 _ hdim _ hneg _ _ => exact X.false_of_h4 hdim hneg

theorem ggSmallD1Input_of_use
    (hUse : ZS.UseInput) : GGSmallD1Input :=
  fun p N _ hcell => ggSmallDepFixLineAt_of_use hUse p N hcell

end CFSG.StandardType

end
