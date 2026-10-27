module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110LgenChain
public import CFSG.RankThree.GF2n.Stroth80.Sec1110StatementAssembly

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem stroth1110_of_chain (hC : CMLmChain) :
    Stroth1110Statement := by
  intro G _ _ M Q Z B _ hc n hw hn ha2 hL
  exact stroth1110_of_inputs hc hw hn ha2 hC (CMLmThree_of_CMLmChain hC)
    (fun _ _ hm hLm => Lgen_le_XbarPre_of_CMLmChain hc hw hn ha2 hC hLm (by omega)) hL

end CFSG.RankThree.GF2n.Stroth80
