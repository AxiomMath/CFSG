module

public import CFSG.Quasithin.Background.JonesParshallG2Two
public import CFSG.Quasithin.Background.B5FinOutAlt
public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Quasithin.Recognition.CertU33Simple
public import CFSG.Quasithin.Recognition.CertU33Perm
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.F2Equiv

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.CosetTable CFSG.Open

open scoped commutatorElement

@[expose] def u33Words2 : Fin 5 → List (Fin 2) :=
  ![[0, 1, 0, 1, 0, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0],
    [1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0],
    [0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1],
    [0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0]]

@[expose] def u33Mats : Fin 5 → Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  ![!![0, 0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 1, 1, 1, 1, 0;
    0, 1, 0, 0, 0, 0, 1, 0;
    1, 1, 1, 0, 0, 1, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 1, 0, 0],
    !![1, 1, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 1, 1, 1;
    0, 0, 0, 1, 0, 1, 0, 0;
    1, 1, 0, 1, 1, 1, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 0, 1, 0;
    0, 1, 0, 0, 0, 1, 0, 1],
    !![1, 1, 1, 1, 1, 1, 0, 0;
    1, 1, 0, 1, 0, 1, 1, 1;
    1, 1, 0, 0, 1, 0, 1, 1;
    0, 1, 1, 0, 1, 1, 0, 0;
    1, 0, 0, 1, 1, 1, 1, 1;
    1, 0, 0, 1, 0, 0, 1, 1;
    1, 1, 1, 0, 1, 0, 0, 1;
    0, 1, 1, 1, 1, 1, 0, 1],
    !![1, 0, 1, 1, 1, 1, 1, 0;
    1, 0, 0, 1, 0, 1, 1, 1;
    1, 1, 0, 0, 1, 0, 0, 1;
    0, 1, 1, 0, 1, 1, 1, 0;
    1, 1, 0, 1, 1, 1, 0, 1;
    1, 1, 0, 1, 0, 0, 1, 1;
    1, 1, 1, 0, 1, 0, 1, 1;
    0, 0, 1, 1, 1, 1, 1, 1],
    !![0, 0, 1, 0, 0, 0, 0, 1;
    1, 0, 1, 0, 1, 1, 1, 1;
    1, 0, 1, 0, 1, 1, 0, 1;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 1, 0, 0, 0;
    0, 0, 1, 1, 1, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 1, 0;
    1, 0, 1, 0, 0, 0, 0, 0]]

@[expose] def u33MatsInv : Fin 5 → Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  ![!![0, 1, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0;
    1, 1, 0, 0, 1, 1, 0, 1;
    0, 0, 0, 0, 0, 1, 1, 0;
    0, 1, 1, 1, 0, 1, 1, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 1, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0],
    !![1, 1, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    1, 1, 1, 0, 0, 1, 1, 1;
    0, 0, 0, 1, 0, 1, 0, 0;
    1, 1, 0, 1, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 0, 1, 0;
    0, 1, 0, 0, 0, 1, 0, 1],
    !![1, 1, 1, 1, 1, 1, 0, 0;
    1, 1, 0, 1, 0, 1, 1, 1;
    1, 1, 0, 0, 1, 0, 1, 1;
    0, 1, 1, 0, 1, 1, 0, 0;
    1, 0, 0, 1, 1, 1, 1, 1;
    1, 0, 0, 1, 0, 0, 1, 1;
    1, 1, 1, 0, 1, 0, 0, 1;
    0, 1, 1, 1, 1, 1, 0, 1],
    !![1, 1, 1, 1, 1, 1, 0, 0;
    1, 1, 0, 1, 0, 1, 1, 1;
    1, 1, 0, 0, 1, 0, 1, 1;
    1, 0, 1, 1, 1, 0, 1, 1;
    0, 1, 1, 1, 0, 1, 1, 0;
    1, 0, 0, 1, 0, 0, 1, 1;
    1, 1, 1, 0, 1, 0, 0, 1;
    0, 1, 1, 1, 1, 1, 0, 1],
    !![0, 0, 0, 0, 1, 1, 0, 1;
    0, 1, 1, 0, 1, 1, 1, 0;
    0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 1, 1, 1, 1, 0, 1;
    0, 1, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 1, 1, 0, 0]]

@[expose] def u33ImgL (i : Fin 5) : ↥(cayleyGroup (ZMod 2)) := wordEval ![g2a, g2b] (u33Words2 i)

end CFSG.Quasithin
