module

public import Certificates.Data.Kernel.EvenSporM22.HS08Defs
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.KC.EvenSporM22

open CFSG.EvenSporadicStandard.M22Std.TabCheck

@[expose] def hs08TabV (t : Tab) : Bool := t.length == 22 && t.all fun e => decide (e < 22)

@[expose] def hs08Pk (t : Tab) : Nat := t.foldr (fun e a => e + 32 * a) 0

@[expose] def hs08Fld : Nat → Nat → Nat
  | c, 0 => c % 32
  | c, j + 1 => hs08Fld (c / 32) j

@[expose] def hs08PConj (a x b : Nat) : Nat :=
  hs08Pk ((List.range 22).map fun j => hs08Fld a (hs08Fld x (hs08Fld b j)))

@[expose] def hs08KeyMod : Nat := 4173

@[expose] def hs08Key (J : List Nat) (a b : Nat) : Nat :=
  (J.map fun x => hs08PConj a x b).sum % hs08KeyMod

@[expose] def HS08PairsOK (P : List (Tab × Tab)) : Prop :=
  ∀ p ∈ P, hs08TabV p.1 = true ∧ hs08TabV p.2 = true ∧ tmul p.1 p.2 = idTab ∧ tmul p.2 p.1 = idTab

instance (P : List (Tab × Tab)) : Decidable (HS08PairsOK P) := by
  unfold HS08PairsOK
  infer_instance

@[expose] def hs08KeysOK (J : List Tab) (P : List (Tab × Tab)) : Bool :=
  CFSG.Decide.bitsetNodup (P.map fun p => hs08Key (J.map hs08Pk) (hs08Pk p.1) (hs08Pk p.2))

end CFSG.KC.EvenSporM22
