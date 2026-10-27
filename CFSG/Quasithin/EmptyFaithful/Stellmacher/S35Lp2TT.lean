module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Lp2Img
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2UC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Lp2

open S35.Ch2 S35.Fin S35.Lp
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem claimTT_II (hS : Sit H M S) (_hII : CaseII H M) : S35.II.ClaimTT H M := by
  have hU : ∀ δ : Geo H M, vtype δ = false → UC δ := fun δ hδ => UC.of_sit hS hδ
  intro β α' m γ' hp hb hT
  obtain ⟨c⟩ := exists_chart2 hS hp.vδ'
  obtain ⟨v, hv, hvs, hv2⟩ := hT
  have hsw : (c.θ ⟨v, hvs⟩).IsSwap := (hasTransp_iff hS hp c (hU _ hp.vδ') hvs).mp hv2
  have hA : c.bar (Vn β) ≤ c.Dl m := c.bar_mono (back_Vn_le_inf hS hp hb)
  have hle : c.bar (Vn β) ≤ That (c.Dl m) :=
    le_That_of_quad hA (bar_Vn_isElemAb hS c) (bar_Vn_isQuad hS hp c)
      (c.mem_bar_of_mem hv hvs) hsw
  intro x hx
  have hxs : x ∈ stab α' ⊓ stab m := back_Vn_le_inf hS hp hb hx
  exact (c.mem_That2_iff_θ hS hp.vδ' (hU _ hp.vδ') hb.1 hxs).mpr
    (hle (c.mem_bar_of_mem hx hxs.1))

end S35.Lp2

end F53.Stellmacher

end CFSG.Quasithin
