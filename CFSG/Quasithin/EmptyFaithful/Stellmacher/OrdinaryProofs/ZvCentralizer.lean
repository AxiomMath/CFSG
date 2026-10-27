module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.OTwoFixedSquare

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Quasithin CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem Zv_inf_centralizer_oTwoRes_eq_bot {H M S : Subgroup G} (hA : F53Amalgam H M S)
    {α β : Geo H M} (hαβ : (graph (H ⊔ M) H M).Adj α β) (hz : Zv β ≤ centerOf (stab β)) :
    Zv α ⊓ Subgroup.centralizer (oTwoRes (stab α) : Set G) = ⊥ := by
  have hadj : α ∈ nbrs β := hαβ.symm
  have hc : centerOf (stab α) = ⊥ := centerOf_eq_bot_of_Zv_central hA hadj hz
  have hVX : Zv α ≤ stab α := (Zv_le_Qv hA α).trans (pCoreOf_le 2 _)
  have hV : IsPGroup 2 (Zv α) := fun g =>
    ⟨1, Subtype.ext (by simpa using isElemAbelian_Zv hA α |>.2 g.1 g.2)⟩
  have hn : stab α ≤ Subgroup.normalizer (Zv α : Set G) := stab_le_normalizer_Zv hA α
  by_contra hne
  have hcen := inf_centralizer_ne_bot_of_oTwoRes hVX hV hn hne
  apply hcen
  have hle : Zv α ⊓ Subgroup.centralizer (stab α : Set G) ≤ centerOf (stab α) :=
    le_inf (inf_le_left.trans hVX) inf_le_right
  rw [hc] at hle
  exact le_bot_iff.mp hle

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

end
