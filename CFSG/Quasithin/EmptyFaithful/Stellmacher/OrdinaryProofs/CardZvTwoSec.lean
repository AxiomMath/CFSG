module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.ZvEdgeCentralizer
public import CFSG.Quasithin.EmptyFaithful.SzF53MZa

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.LieType.BorelTits CFSG.Quasithin.F53Mod Equiv

variable {G : Type} [Group G] [Finite G]

theorem card_Zv_eq_two_of_sec {H M S : Subgroup G} (hA : F53Amalgam H M S) {δ μ : Geo H M}
    (_hδ : vtype δ = false) (hadj : (graph (H ⊔ M) H M).Adj δ μ) (hz : Zv μ ≤ centerOf (stab μ))
    (hsec : IsOrthSec (stab δ) ⊥ (Zv δ) ∨ IsNatSec (stab δ) ⊥ (Zv δ)) :
    Nat.card (Zv μ) = 2 := by
  have hS : IsSylowTwoOf (stab δ ⊓ stab μ) (stab δ) := sylow_stab_inf_left hA hadj
  have hZ : Zv δ ⊓ Subgroup.centralizer ((stab δ ⊓ stab μ : Subgroup G) : Set G) = Zv μ :=
    Zv_inf_centralizer_edge_eq hA hadj hz
  rw [← hZ]
  rcases hsec with h | h
  · exact IsModelSec.card_fix_sylow (Or.inl rfl) h hS
  · exact IsModelSec.card_fix_sylow (Or.inr rfl) h hS

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

end
