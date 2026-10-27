module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even20AD

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem out20bc (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M} (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β) (h19 : Out19 α β) :
    Out20bc α β where
  C_normal := by
    rw [← h19.C_eq]
    exact sup_le (E20A.Mab_le_normalizer hA h26 hs hβ h.Vst_normal).2
      (E20A.stab_le_normalizer hA h26 hs hβ).2
  Q_normal := sup_le (E20A.Mab_le_normalizer hA h26 hs hβ h.Vst_normal).1
    (E20A.stab_le_normalizer hA h26 hs hβ).1
  relIndex_C_Q := E20A.relIndex_Cst_Qgrp hA h26 hs hb hβ h.card_Vn h.Vst_normal h19.C_eq
  relIndex_Q_P := E20A.relIndex_Qgrp_edge hA h26 hs hb hβ h.card_Vn

end CFSG.Quasithin.F53.Stellmacher.S43.Even
