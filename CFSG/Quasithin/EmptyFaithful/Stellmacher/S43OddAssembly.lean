module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddCaseLFive
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddCore7
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddThreeC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem false_of_odd_caseL (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb3 : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α)
    (hL : 2 ^ 7 ≤ Nat.card (Vn β)) : False := by
  by_cases h3 : bMin H M = 3
  · exact false_of_caseL_three hA h26 hs h3 hβ hL
  · obtain ⟨k, hk⟩ := ho
    exact false_of_caseL_five hA h26 hs ⟨k, hk⟩ (by omega) hβ hL

theorem false_of_odd_caseS_five (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb3 : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α)
    (h4 : Nat.card (Vn β) = 2 ^ 6) (h5 : bMin H M = 5) : False :=
  bMin_ne_five_of_caseS hA h26 hs ho hb3 hβ h4 h5

theorem false_of_odd (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hg7 : Gap7At H M) (hend : OddEndAt H M) : False := by
  have hb1 := hs.b1
  have hb3 : 3 ≤ bMin H M := by
    obtain ⟨k, hk⟩ := ho
    omega
  obtain ⟨β, hβ⟩ := hs.exists_adj hA
  have hβ' : β ∈ nbrs α := hβ
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  rcases hs.card_Vn_cases hA h26 hb3 hβv with h | h | h
  ·
    by_cases h5 : bMin H M = 5
    · exact false_of_odd_caseS_five hA h26 hs ho hb3 hβ' h h5
    · by_cases h3 : bMin H M = 3
      · exact hg7 S hA h26 α hs h3 β hβ' h
      · obtain ⟨k, hk⟩ := ho
        exact hend S hA h26 α hs ⟨k, hk⟩ (by omega) β hβ' h
  · exact false_of_odd_caseL hA h26 hs ho hb3 hβ' (le_of_eq h.symm)
  · exact false_of_odd_caseL hA h26 hs ho hb3 hβ' (by rw [h]; norm_num)

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
