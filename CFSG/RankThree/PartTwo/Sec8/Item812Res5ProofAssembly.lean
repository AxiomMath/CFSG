module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofKFacts
public import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofSym
public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofPa
public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem fin812Sylow_of_res5 (hPa : Fin812PaExp)
    (hBq : Fin812BEq) (hQR : Fin812QR) (hBw : Fin812BWeak) : Fin812Sylow :=
  fin812Sylow_of_res4 (fin812PaSplit_of_exp hPa) hBq hQR hBw kF812WreathCent_holds
    kF812E27Fuse_holds

theorem pair84Gamma_of_xy (h45 : Sec4.Item4_5) (h87 : Item87) (hXY : Item89XY) :
    Pair84Gamma := by
  intro G _ _ A c L a b X n h e Le hrel
  obtain ⟨Y, hY, hIJ⟩ := h87 G A c L a b X n h
  exact Item87Res2Proof.pair84Gamma_of_projSp h45 h (hXY G A c L a b X n h Y hY hIJ).1 hrel

theorem pair84Sym_of_xy (h45 : Sec4.Item4_5) (h87 : Item87) (hXY : Item89XY) : Pair84Sym :=
  pair84Sym_of_gamma (pair84Gamma_of_xy h45 h87 hXY)

end CFSG.RankThree.PartTwo.Sec8
