module

public import Certificates.Data.Kernel.L34W.Model
public import Certificates.Data.Kernel.Multipliers.Mono
public import Certificates.Data.TBLitL34PFieldCheck

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

@[expose] noncomputable def fourthC (T : Nat → Nat) (k : Nat) : Bool :=
  strictB (mulC T (16 * k) (16 * k)) fun s =>
    strictB (mulC T s s) fun c => Nat.beq c 0 || Nat.beq c 8

@[expose] noncomputable def fieldK (T : Nat → Nat) : Bool :=
  CFSG.KC.Mono.allR 0 64 fun k =>
    !(comp 42 (wordTab (tg k)) r₂T == comp 42 r₂T (wordTab (tg k))) || fourthC T k

@[expose] noncomputable def alphaZK (A : Nat → Nat) : Bool :=
  ent A 1 64 % 48 / 12 == 1 && ent A 1 64 % 12 / 3 == 0 &&
    ent A 1 65 % 48 / 12 == 3 && ent A 1 65 % 12 / 3 == 3

end CFSG.KC.L34W

end
