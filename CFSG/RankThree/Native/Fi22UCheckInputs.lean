module

public import CFSG.Monster.B.Fischer.Fi22Outer
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Monster.B.Fischer.Fi22Outer
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.RankThree.Native.Fi22U

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Fischer

@[expose] def fi22LexLt (v w : Fin 6 → F4) : Prop :=
  List.Lex (· < ·) (List.ofFn fun i => (v i).code) (List.ofFn fun i => (w i).code)

instance (v w : Fin 6 → F4) : Decidable (fi22LexLt v w) := by
  unfold fi22LexLt
  infer_instance

@[expose] def fi22Tv (v x : Fin 6 → F4) : Fin 6 → F4 := x + fi22Herm v x • v

end CFSG.RankThree.Native.Fi22U
