module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Quot
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Reduce

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Core


theorem stroth63b_of_inputs (I : HS6.Inputs) (hS : HS6.Stroth65XSplitStatement)
    (h63a : Stroth63aStatement) : Stroth63bStatement := by
  intro G _ _ M Q Z B hc n t hs m hm hΩ
  have hn := h63a G M Q Z B hc n t hs m hm hΩ
  obtain ⟨X, hQX, hXR, hNX, hNXQ, hcen, -⟩ := hS G M Q Z B hc n t hs m hm hn hΩ
  have e : HS6.Env hc n t m X := ⟨hs, hm, hn, hΩ, hQX, hXR, hNX, hNXQ, hcen⟩
  exact e.stronglyClosedMod_of I fun h hh hL => e.conj_CN_eq I hh hL

end Core

section Certs

theorem stroth63b_holds : Stroth63bStatement :=
  stroth63b_of_inputs ⟨stroth34Statement_unconditional,
    stroth310Root_of_34 stroth34Statement_unconditional, stroth51Statement_unconditional,
    strothNtStatement_unconditional⟩ stroth65XSplit_holds
    (stroth_6_3a stroth34Statement_unconditional stroth6LBStatement_holds)

end Certs

end CFSG.RankThree.GF2n.Stroth80
