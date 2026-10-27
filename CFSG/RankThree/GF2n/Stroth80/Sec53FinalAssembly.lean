module

public import CFSG.RankThree.GF2n.Stroth80.Sec53aUncond
public import CFSG.RankThree.GF2n.Stroth80.Sec53bcUncond
public import CFSG.RankThree.GF2n.Stroth80.Sec53dIndecVoneProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Certs

theorem stroth53dStatement_holds (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) : Stroth53dStatement := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane C N R V W₁ V₁ hC hN hR hV hV₁ hW₁
  subst hC hN hR hV hV₁ hW₁
  exact ⟨sec53_sp_comm_CN_vone_le_Z h34 h51 hc hs hsp hr hplane,
    sec53_sp_comm_Q_le_Wt_vone h34 h51 hc hs hsp hr hplane,
    stroth53IndecVone_holds h34 hRoot h51 G M Q Z B hc n t hs hsp r hr hplane⟩

theorem stroth53Statement_holds (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) : Stroth53Statement :=
  ⟨stroth53aStatement_holds h34 hRoot h51,
   stroth53bStatement_holds h34 hRoot h51,
   stroth53cStatement_holds h34 hRoot h51,
   stroth53dStatement_holds h34 hRoot h51,
   stroth_5_3e stroth34Statement_unconditional
       (stroth310NotQB_of_34 stroth34Statement_unconditional)⟩

end Certs

end CFSG.RankThree.GF2n.Stroth80
