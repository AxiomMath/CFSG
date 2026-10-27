module

public import CFSG.Quasithin.H13.AS91Sec2Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties

public section

namespace CFSG.Quasithin.H13.AS91.Sp4.Model

open CFSG.Quasithin.H13.AS91.Sp4 Finset

@[expose] def B4 : Type := Fin 16

instance : DecidableEq B4 := inferInstanceAs (DecidableEq (Fin 16))

instance : Fintype B4 := inferInstanceAs (Fintype (Fin 16))

instance : Zero B4 := ⟨(0 : Fin 16)⟩

instance : Add B4 :=
  ⟨fun a b => ⟨(a : Fin 16).val ^^^ (b : Fin 16).val,
    Nat.xor_lt_two_pow (n := 4) (a : Fin 16).isLt (b : Fin 16).isLt⟩⟩

end CFSG.Quasithin.H13.AS91.Sp4.Model
