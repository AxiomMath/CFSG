module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddTwelve
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddFC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem false_of_caseL_five (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (h5 : 5 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α)
    (hL : 2 ^ 7 ≤ Nat.card (Vn β)) : False := by
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hL' : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ) := fun δ hδ => by
    rw [card_Vn_eq (Sit43.vtype_true_of_adj hs.vα hδ) hβv]; exact hL
  have hamo := atMostOneNoncentral_of_caseL hA h26 hs ho h5 hL'
  have h6 := card_Vn_eq_of_atMostOne hA h26 hs (by omega) hβ hamo
  omega

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
