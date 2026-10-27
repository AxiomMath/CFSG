module

public import Certificates.Data.CFSGNative.MultRes.Witnesses
public import Certificates.Data.CFSGNative.ComponentPrimary.BabyMonster
public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.F2
public import Certificates.Data.CFSGNative.SectionRank.F3
public import Certificates.Data.CFSGNative.SectionRank.F2Fast

public section

namespace CFSG.SectionRank.Native

set_option maxRecDepth 4000

@[expose] def thSevenRot : SqData :=
  { thMultData7 with rh := 20, oh := 4, a := 6, b := 5, c := 1, d := 1 }

@[expose] def bSevenRot : SqData :=
  { bMultSeven () with
    nregs := 9
    prog := (bMultSeven ()).prog.take 56 ++ [Op.pow 1 4 8] ++ (bMultSeven ()).prog.drop 56
    rh := 8
    oh := 4
    a := 6
    b := 5
    c := 1
    d := 1 }

@[expose] def suzFiveWordX : String :=
  "2010201020101011010202010101010202010202011020101020101020201010201010102201020101010201\
    0102020101020101101020201010101020101010202010101010101020102020101020201020101010101020\
    2010102020201010102020101010102010101010202010102020202010101010202010202010201020202020\
    1010101020102010102010102010201010101020202"

@[expose] def suzFiveWordY : String :=
  "2020201020201010202020101010101102020202020102010201010101020202201020202020101020202010\
    1020200102020102010202020201010202010101010202020201020202020101020201010102020110101020\
    00002020002010202020201010101020101010202010102020102020101010"

@[expose] def suzFiveWordH : String :=
  "0101010102010101102011010101020101010202010101020201101010202010101020201010102020101020\
    2020101010202020201020102020101010101020201020101011010101020201010102010101010202020201\
    0202020201010101020101010102020202010201020101010102020202010201020201020201020102020202\
    0101010102010"

@[expose] def wordOps (acc : Nat) (s : String) : List Op :=
  match s.toList.map (fun c => c.toNat - 48) with
  | [] => []
  | l :: ls => Op.pow 1 l acc :: ls.map fun l' => Op.mul acc l' acc

@[expose] def suzFiveRot : SqData :=
  { suzMultData with
    nregs := 6
    rx := 3
    ry := 4
    rh := 5
    r := 5
    oh := 3
    a := 1
    b := 3
    c := 4
    d := 3
    t := 0
    prog := Op.pow 2 1 2 :: (wordOps 3 suzFiveWordX ++ wordOps 4 suzFiveWordY ++
      wordOps 5 suzFiveWordH) }


end CFSG.SectionRank.Native
