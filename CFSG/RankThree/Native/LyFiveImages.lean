module

public import CFSG.RankThree.Native.LyFiveArrays
public meta import CFSG.Monster.B.Fischer.InducedData
public meta import CFSG.RankThree.Native.LyFiveArrays
public meta import CFSG.RankThree.Native.LyFiveData
public import CFSG.RankThree.Native.LyFiveImagesInputs
public import Certificates.Certificate8131

public section

namespace CFSG.RankThree.Native

@[expose] def fiveMat4 (X : Array (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  Matrix.of fun i j => X[4 * i.val + j.val]!

theorem ly_five_tb_nodup : lyFiveTbArr.toList.Nodup :=
  Certificates.certificate8131

end CFSG.RankThree.Native
