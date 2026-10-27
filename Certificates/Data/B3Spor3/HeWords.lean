module

public import Certificates.Data.B3Spor3.He

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3S3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def heC0Words (g : Array (Array ℕ)) : Bool :=
  g.size == 3 && validA 8330 g[0]! && validA 8330 g[1]! && validA 8330 g[2]! &&
    eqA 8330 (powArr 8330 g[0]! 3) (idA 8330) &&
    eqA 8330 (powArr 8330 (compA 8330 (compA 8330 g[1]! g[2]!) g[2]!) 12) (idA 8330) &&
    eqA 8330 (powArr 8330 (compA 8330 (compA 8330 g[1]! g[1]!) g[2]!) 12) (idA 8330)

@[expose] def heC0WordsCheck (_ : Unit := ()) : Bool := heC0Words heS3C0Gens

end CFSG.HardMathSupport.Solomon.Coordinator.B3S3
