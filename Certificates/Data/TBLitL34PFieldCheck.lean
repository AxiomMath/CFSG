module

public import Certificates.Data.GrSLitL34FactsRealBCheck

public section

namespace CFSG.ComponentClassification.TBLit.L34P

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

@[expose] def fourthM (k : ℕ) : MElt :=
  mulM (mulM (k, 0, 0) (k, 0, 0)) (mulM (k, 0, 0) (k, 0, 0))

@[expose] def alphaZOK : Bool :=
  (alphaEntry 1 64).2.1 == 1 && (alphaEntry 1 64).2.2.1 == 0 &&
    (alphaEntry 1 65).2.1 == 3 && (alphaEntry 1 65).2.2.1 == 3

@[expose] def fourthOK : Bool :=
  allBelow 64 fun k => !(comp 42 (wordTab (tg k)) r₂T == comp 42 r₂T (wordTab (tg k))) ||
    (fourthM k == (0, 0, 0) || fourthM k == (0, 2, 0))

@[expose] def l34pFieldOK : Bool := alphaZOK && fourthOK

end CFSG.ComponentClassification.TBLit.L34P
