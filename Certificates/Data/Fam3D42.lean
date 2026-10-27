module

public import Certificates.Data.Item434D42
public import Certificates.Data.L28Presentation
public meta import Certificates.Data.Item434D42
public meta import Certificates.Data.L28Presentation
public meta import Certificates.Data.K426Checks

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Fam3D42

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.RankThree.PartTwo.KFacts.K426 CFSG.RankThree.PartTwo.Sec4.Item434D42
  CFSG.HardMathSupport.Dickson.I271.L28Presentation

@[expose] def lWordA : List (Fin 3 × Bool) :=
  [(1, true), (1, true), (1, true), (1, true), (2, true), (1, true)]

@[expose] def lWordB : List (Fin 3 × Bool) :=
  [(1, true), (2, true), (1, true), (2, true), (1, true), (2, true)]

@[expose] def lGens (_ : Unit := ()) : Array (Array ℕ) :=
  #[evalWA 2457 d4CAGens lWordA, evalWA 2457 d4CAGens lWordB]

@[expose] def lCert (_ : Unit := ()) : ArrCert := enumBfs 2457 (lGens ()) d4Keys 520

@[expose] def caseA3Check (_ : Unit := ()) : Bool :=
  let L := lGens ()
  derivedLeOK 2457 d4CAGens L d4Keys (lCert ()) 504 &&
    allLt L.size (fun l => d4CACert.pts.toList.any (eqA 2457 L[l]!)) &&
    wordsOneOK 2457 L l28Words

end CFSG.HardMathSupport.Dickson.Bal207.Fam3D42
