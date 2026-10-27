module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even20BE

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace E20B

theorem relIndex_W_eq_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β)
    (h19 : Out19 α β) (h20 : Out20bc α β) :
    (Subgroup.centralizer (Cst β : Set G)).relIndex (Wcomm α) = 2 := by
  have h2 := relIndex_W_le_two hA h26 hs hb hβ h h20
  have h1 : (Subgroup.centralizer (Cst β : Set G)).relIndex (Wcomm α) ≠ 1 := fun h1 =>
    not_le_centralizer hA h26 hs hb hβ h h19 h20 (Subgroup.relIndex_eq_one.mp h1)
  have h0 : (Subgroup.centralizer (Cst β : Set G)).relIndex (Wcomm α) ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  omega

theorem not_Cst_le_Mcent (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β)
    (h19 : Out19 α β) (h20 : Out20bc α β) : ¬ Cst β ≤ Mcent α := fun hle =>
  not_le_centralizer hA h26 hs hb hβ h h19 h20
    (Subgroup.le_centralizer_iff.mpr (hle.trans inf_le_right))

end E20B

theorem out20 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M} (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β) (h19 : Out19 α β)
    (h20 : Out20bc α β) : Out20 α β where
  toOut20bc := h20
  Q_sup := E20B.Qgrp_sup_Qv hA h26 hs hb hβ h h19 h20
  relIndex_inf := (E20B.relIndex_Cst_inf hA h26 hs hb hβ h h19 h20).1
  comm_le := E20B.comm_inf_le_Cst hA h26 hs hb hβ h h19 h20
  relIndex_W := E20B.relIndex_W_eq_two hA h26 hs hb hβ h h19 h20
  not_C_le_M := E20B.not_Cst_le_Mcent hA h26 hs hb hβ h h19 h20

end CFSG.Quasithin.F53.Stellmacher.S43.Even
