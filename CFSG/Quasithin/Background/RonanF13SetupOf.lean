module

public import CFSG.Quasithin.Background.RonanF13Hall
public import CFSG.Quasithin.Background.F1Cartan

public section

namespace CFSG.Quasithin.RonanF13

universe u

variable {G : Type u} [Group G] [Finite G]

theorem F13Setup.of_hyp111R {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S) :
    F13Setup L1 L2 S where
  finS := h.hyp.h1.finite
  pS := h.hyp.h1.pgroup
  finL1 := inferInstance
  finL2 := inferInstance
  syl1 := h.hyp.h1.sylow
  syl2 := h.hyp.h2.sylow
  comm1 := h.r1.comm
  comm2 := h.r2.comm
  b2_le_nL1 := h.hyp.h1.borel_le
  b1_le_nL2 := h.hyp.h2.borel_le
  pcore1 := F7.isSylowTwoOf_pCoreOf_le h.hyp.h1.sylow
  pcore2 := F7.isSylowTwoOf_pCoreOf_le h.hyp.h2.sylow
  b2_le_nb1 := F1.borelOf_le_normalizer_borelOf h
  b1_le_nb2 := F1.borelOf_le_normalizer_borelOf h.symm
  s_le_nb1 := F1.le_normalizer_borelOf h.hyp.h1.normalizes
  s_le_nb2 := F1.le_normalizer_borelOf h.hyp.h2.normalizes
  bigB_le_ns1 := (F1.bigB_le_normalizer_sylow h).1
  bigB_le_ns2 := (F1.bigB_le_normalizer_sylow h).2
  solvable := F1.isSolvable_bigB h

end CFSG.Quasithin.RonanF13

end
