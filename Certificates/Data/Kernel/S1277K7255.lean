module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zzE
public import Certificates.Data.Kernel.S1277KML
public import Mathlib.Data.List.Permutation

public section

namespace CFSG.KC.C7255

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277ML CFSG.KC.S1277Gm

@[expose] noncomputable def stabK (Q : List ℕ) (c : ℕ) : ℕ :=
  cntL (fun p => andB (Nat.beq (appP p c) c) (Nat.beq (appP p 1) 1)) Q

@[expose] def fins : List (Fin 6) := [0, 1, 2, 3, 4, 5]

@[expose] def fresh (x : Fin 6) (L : List (Fin 6)) : Bool := !(L.contains x)

@[expose] def cycT (t l : List (Fin 6)) : Bool :=
  (List.range 7).all fun b => !cycOK b (fl l) || !cycMoved b (fl l) || l == t

@[expose] def cycK : Bool :=
  fins.all fun a0 => fins.all fun a1 => !fresh a1 [a0] || fins.all fun a2 =>
    !fresh a2 [a0, a1] || fins.all fun a3 => !fresh a3 [a0, a1, a2] || fins.all fun a4 =>
      !fresh a4 [a0, a1, a2, a3] || fins.all fun a5 => !fresh a5 [a0, a1, a2, a3, a4] ||
        cycT fins [a0, a1, a2, a3, a4, a5]

end CFSG.KC.C7255

end
