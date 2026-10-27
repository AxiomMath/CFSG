module

public import CFSG.Quasithin.Background.HFCodeInputs

public section

namespace CFSG.Quasithin.H.Mathieu

@[expose] def u22Masks : List ℕ :=
  [0, 19, 194, 209, 354, 369, 416, 435, 513, 530, 707, 720, 867, 880, 929, 946]

@[expose] def predU22 (l : List T22s2.Elem) : Bool :=
  l.length != 5 || codeFixMasks22 l == u22Masks

end CFSG.Quasithin.H.Mathieu
