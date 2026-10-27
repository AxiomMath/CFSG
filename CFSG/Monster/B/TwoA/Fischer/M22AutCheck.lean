module

public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data
public import Certificates.Certificate3164
public meta import CFSG.Sporadic.Schreier.ImagePairs

public section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Th.Native

theorem m22_word_ab2 :
    ordW 22 [toTable m22gA, toTable m22gB, toTable m22gB] 5 = true :=
  Certificates.certificate3164.1

theorem m22_pair5_count :
    pairCount (orderTables m22Certificate 2) (orderTables m22Certificate 4)
      (fun x y => pairTest 22 11 6 2 4 x y && ordW 22 [x, y, y] 5) = 887040 :=
  Certificates.certificate3164.2

end CFSG.Monster.B.TwoA.Fischer
