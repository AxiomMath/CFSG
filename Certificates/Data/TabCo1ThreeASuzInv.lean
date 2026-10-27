module

public import Certificates.Data.TabSuzFuse
public meta import Certificates.Data.TabSuzFuse

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeASuzInv

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse

@[expose] def tupA : Array (Array Nat) :=
  #[#[1166, 1013, 1730, 827, 1418, 517], #[1228, 676, 1173, 756, 4, 1651],
    #[1354, 1457, 447, 1364, 552, 295]]

@[expose] def tupB : Array (Array Nat) :=
  #[#[1351, 1695, 1282, 496, 1181, 1148], #[0, 1, 2, 826, 599, 1182],
    #[12, 808, 1179, 917, 1059, 1750]]

@[expose] def tupY : Array (Array Nat) :=
  #[#[115, 1049, 1777, 857, 1607, 1641], #[1284, 1648, 1068, 1480, 1022, 8],
    #[691, 1420, 439, 1584, 1602, 765]]

@[expose] def invAtOK (L : Array Level) (c : Array Nat) (tp : Array (Array Nat)) : Bool :=
  let s := rebuild L tp[0]!
  let t := rebuild L tp[1]!
  let t' := rebuild L tp[2]!
  validA 1782 s && inP L s && validA 1782 t && inP L t && validA 1782 t' && inP L t' &&
    eqA 1782 (compA 1782 s s) (idA 1782) &&
    eqA 1782 (compA 1782 (compA 1782 s c) (compA 1782 s c)) (idA 1782) &&
    eqA 1782 (compA 1782 t t) (idA 1782) && eqA 1782 (compA 1782 t' t') (idA 1782) &&
    eqA 1782 (compA 1782 t c) (compA 1782 c t) && eqA 1782 (compA 1782 t' c) (compA 1782 c t') &&
    eqA 1782 (powArr 1782 (compA 1782 t t') 3) (idA 1782) &&
    !(eqA 1782 (compA 1782 t t') (idA 1782))

@[expose] def suzInvCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  invAtOK L (xAArr L) tupA && invAtOK L (xBArr L) tupB && invAtOK L (yArr L) tupY

end CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeASuzInv
