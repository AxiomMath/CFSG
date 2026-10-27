module

public import Certificates.Data.Kernel.Griess13.Packed

public section

namespace CFSG.KC.SlpM

open CFSG.KC.G13

@[expose] noncomputable def codeC (c : Nat) : List Char :=
  Bool.rec (motive := fun _ => List Char) (natC (Nat.shiftRight c (nat_lit 1)))
    (List.cons '-' (natC (Nat.shiftRight c (nat_lit 1)))) (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def wordC (w : List Nat) : List Char := [','].intercalate (w.map codeC)

@[expose] noncomputable def wordsC (W : List (List Nat)) : List Char := [';'].intercalate (W.map wordC)

@[expose] noncomputable def pairC (p : Nat × List Nat) : List Char :=
  natC p.1 ++ List.cons '|' ([','].intercalate (p.2.map natC))

@[expose] noncomputable def pairsC (P : List (Nat × List Nat)) : List Char :=
  [';'].intercalate (P.map pairC)

end CFSG.KC.SlpM

end
