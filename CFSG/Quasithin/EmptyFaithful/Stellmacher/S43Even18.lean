module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even18D

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hyp18_of_split (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α)
    (hD4 : Nat.card (Vn β) = 2 ^ 6) (hWQ : ⁅Wn α, Qv α⁆ ≤ Zv α)
    (hsec : IsOrthSec (stab α) (Zv α) (Wcomm α)) (hsup : Estar α ⊔ Wcomm α = Wn α)
    (hinf : Estar α ⊓ Wcomm α = Zv α) : Hyp18 α β := by
  have hZN : Zv α ≤ Wcomm α := hinf ▸ inf_le_right
  have hNW : Wcomm α ≤ Wn α := hsup ▸ le_sup_right
  have hNs : Wcomm α ≤ stab α := hNW.trans ((hs.Wn_le_Qv hA hb).trans (pCoreOf_le 2 _))
  have hVN : Vst β ≤ Wcomm α :=
    Subgroup.commutator_mono (hs.Vn_le_Wn hA h26 hβ) (Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ))
  exact
    { card_Vn := hD4
      comm_Wn_Qv := hWQ
      sec := hsec
      sup_eq := hsup
      inf_eq := hinf
      Vn_inf_Estar := C18.Vn_inf_Estar_eq hA h26 hs hb hβ
      proj := C18.proj_eq hA h26 hs hb hβ hsec hsup hinf hD4
      Vst_normal := C18.Mab_le_normalizer_Vst hA h26 hs hb hβ hD4 hsec hZN hNs hVN }

theorem hyp18_of_transvec (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 4 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α)
    (hD4 : Nat.card (Vn β) = 2 ^ 6) (hWQ : ⁅Wn α, Qv α⁆ ≤ Zv α) {x : G} (hx : x ∈ stab α)
    (hxt : IsTransvec 1 x (Zv α) (Wn α)) : Hyp18 α β := by
  obtain ⟨hsec, hsup, hinf⟩ := C18.split18 hA h26 hs hb hWQ hx hxt
  exact hyp18_of_split hA h26 hs (by omega) hβ hD4 hWQ hsec hsup hinf

theorem claim18 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (_he : Even (bMin H M)) (hb : 4 ≤ bMin H M) (h17 : Claim17 α)
    {β : Geo H M} (hβ : β ∈ nbrs α) : Hyp18 α β := by
  obtain ⟨hD4, hWQ⟩ := claim18a hA h26 hs hb h17 hβ
  obtain ⟨x, hx, -, hxt⟩ := h17
  exact hyp18_of_transvec hA h26 hs hb hβ hD4 hWQ hx hxt

end CFSG.Quasithin.F53.Stellmacher.S43.Even
