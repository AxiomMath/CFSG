
module

public import CFSG.Quasithin.Background.HMathieuCodeMask
public import CFSG.Quasithin.Background.HMathieuSyl22
public import CFSG.Quasithin.Background.HMathieuSyl23
public import CFSG.Quasithin.Background.HMathieuSyl24
public import CFSG.Quasithin.Background.HMathieuFacts24Base
public meta import CFSG.Quasithin.Background.HMathieuCodeMask
public meta import CFSG.Quasithin.Background.HMathieuSyl22
public meta import CFSG.Quasithin.Background.HMathieuSyl23
public meta import CFSG.Quasithin.Background.HMathieuSyl24
public meta import CFSG.Quasithin.Background.HMathieuFacts24Base
public meta import CFSG.Monster.Code.Basis

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

@[expose] def matsOfC10 (T : PT 24) : Array (List ℕ) := T.elems.map fun a => matOf 10 (actC10 a)

@[expose] def matsOfC11 (T : PT 24) : Array (List ℕ) := T.elems.map fun a => matOf 11 (actC11 a)

@[expose] def matsC22 : Array (List ℕ) := matsOfC10 T22s2

@[expose] def matsC23 : Array (List ℕ) := matsOfC11 T23s2

@[expose] def matsC24 : Array (List ℕ) := matsOfC11 T24s2

@[expose] def inv23Arr : Array ℕ :=
  #[0, 22, 3, 2, 10, 12, 16, 7, 8, 19, 4, 13, 5, 11, 18, 15, 6, 17, 14, 9, 20, 21, 1, 23]

end CFSG.Quasithin.H.Mathieu
