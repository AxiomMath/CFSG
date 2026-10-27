module

public import CFSG.Quasithin.H13.A5SitY
public import CFSG.Quasithin.H13.A5L1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace A5.Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : A5.Setting G T L V)

@[expose] noncomputable def toA5Sit (h1323 : Input1323Two) (h1326 : Input1326Two)
    (h1336 : Input1336) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) : A5Sit G T V S.V1 S.V3 S.L1 H where
  L := L
  h13 := S.h13
  hF := S.hypF91 h1323 hH
  L1_eq := rfl
  card_V := S.card_V
  card_V3 := S.card_V3
  nonabelian := hna
  isPGroup_sup := fun _ hg hlt => S.isPGroup_sup_of_lt h1323 h1326 h1336 hH hg hlt
  comm_centralizer := S.hyp_F956 h1323 H
  commutator_V_L1 := S.commutator_V_L1
  commutator_V3_L1 := S.commutator_V3_L1
  NV_le := S.NV_le_M

@[expose] noncomputable def toA5SitY
    (h1323 : Input1323Two) (h1326 : Input1326Two)
    (h1336 : Input1336) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) :
    A5SitY (S.toA5Sit h1323 h1326 h1336 hH hna) S.L1 :=
  (S.toA5Sit h1323 h1326 h1336 hH hna).toA5SitY (S.cL1 : G) S.cL1_mem S.cL1_cube S.cL1_not_mem
    fun _ hx => S.L1_decomp hx

end A5.Setting

end CFSG.Quasithin.H13
