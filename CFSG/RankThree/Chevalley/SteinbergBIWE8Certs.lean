
module


public import Certificates.Certificate18004

public noncomputable section

namespace CFSG.RankThree.Chevalley.WeylE8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.WE8.Native

theorem card_isConj_y0 : Nat.card {u : W8 // IsConj y0 u} = 15120 :=
  Certificates.certificate18004.2.2.2.1

theorem card_skew_le : Nat.card {w : W8 // SgnSym (-1) w} ≤ 15120 :=
  Certificates.certificate18004.2.2.2.2.2

end CFSG.RankThree.Chevalley.WeylE8
