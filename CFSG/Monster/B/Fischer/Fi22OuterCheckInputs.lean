module

public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Monster.B.Fischer.Fi22OuterArrays
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native

@[expose] def layoutOK (b : ByteArray) (w n m : Nat) : Bool :=
  b.size == m * (w * n + 1) && allLt m fun L => b.get! (L * (w * n + 1) + w * n) == 10

@[expose] def wordsOK (k s : Nat) (D : List (List Int)) : Bool :=
  D.length + k == s && allLt s fun j => decide (j < k) || lettersOK j (fi22WordsArr k s D)[j]!

end CFSG.Monster.B.Fischer
