module

public import CFSG.Quasithin.Recognition.St84.Hyp

public section

namespace CFSG.Quasithin.St84

open CFSG.Open

namespace Setup

variable {V : Type*} {Γ : SimpleGraph V} {G : Type*} [Group G] [MulAction G V]

structure CentralZData (Y : Setup Γ G) : Prop where
  card_Z_zero : Nat.card (Y.Z 0) = 2
  centerOf_S : centerOf Y.S = Y.Z 0
  L_zero_le_centralizer : Y.L 0 ≤ Subgroup.centralizer (Y.Z 0 : Set G)
  Z_zero_le_Q_one : Y.Z 0 ≤ Y.Q 1
  iSup_conj_L_one : (⨆ g ∈ Y.L 1, (Y.Z 0).map (MulAut.conj g).toMonoidHom) = Y.Z 1
  card_Z_one : Nat.card (Y.Z 1) = 4
  Z_one_le_Q_zero : Y.Z 1 ≤ Y.Q 0

end Setup

end CFSG.Quasithin.St84
