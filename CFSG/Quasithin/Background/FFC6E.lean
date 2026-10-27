module

public import CFSG.Quasithin.Background.FFC6D
public import CFSG.Quasithin.Background.FFC4Tr1

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace B59

section Ident

variable {V : Type} [CommGroup V]

theorem map_commV_aut {L : Subgroup (MulAut V)} {W : Subgroup V} (hst : L ≤ stabSub W) :
    (commV (autSub L W)).map W.subtype = commSub W L := by
  rw [commV_eq_commSub, map_commSub_autSub hst, Subgroup.map_top, Subgroup.range_subtype]

theorem map_fixV_inf_commV_aut {L : Subgroup (MulAut V)} {W : Subgroup V} (hst : L ≤ stabSub W) :
    (fixV (autSub L W) ⊓ commV (autSub L W)).map W.subtype = fixV L ⊓ commSub W L := by
  rw [Subgroup.map_inf _ _ W.subtype W.subtype_injective, map_commV_aut hst,
    map_subtype_fixV_autSub hst]
  have : commSub W L ≤ W := commSub_le_of_invariant (fun x hx w hw => (hst hx w).2 hw)
  ext v
  constructor
  · rintro ⟨⟨-, hv⟩, hc⟩
    exact ⟨hv, hc⟩
  · rintro ⟨hv, hc⟩
    exact ⟨⟨this hc, hv⟩, hc⟩

theorem binaryNaturalSL_lift {L : Subgroup (MulAut V)} {W : Subgroup V} (hst : L ≤ stabSub W)
    (hf : ∀ g ∈ L, (∀ v ∈ W, g v = v) → g = 1) (hcomm : commV L = commSub W L) {d n : ℕ}
    (h : BinaryNaturalSL (autSub L W) (commV (autSub L W))
      (fixV (autSub L W) ⊓ commV (autSub L W)) d n) :
    BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) d n := by
  obtain ⟨K, hK, hfin, hc, hr⟩ := h
  refine ⟨K, hK, hfin, hc, ?_⟩
  have := realizes_map hst hf hr
  rwa [map_commV_aut hst, map_fixV_inf_commV_aut hst, ← hcomm] at this

theorem directSum_lift {L : Subgroup (MulAut V)} {W : Subgroup V} (hst : L ≤ stabSub W)
    (hf : ∀ g ∈ L, (∀ v ∈ W, g v = v) → g = 1) (hcomm : commV L = commSub W L) {D : FFModel}
    {k : ℕ} (h : DirectSumOfCopies (autSub L W) (commV (autSub L W)) ⊥ D k) :
    DirectSumOfCopies L (commV L) ⊥ D k := by
  have := directSum_map hst hf h
  rwa [map_commV_aut hst, Subgroup.map_bot, ← hcomm] at this

end Ident

end B59

end FFC

end CFSG.Quasithin
