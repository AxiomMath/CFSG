module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveInputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveInputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24MooreNative

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveNative

set_option compiler.extract_closed false

@[expose] def extendChain (com : Nat → Nat → Bool) (F : List Nat) : Nat → List Nat → Option (List Nat)
  | 0, p => some p
  | n + 1, p => F.findSome? fun v =>
      if p.contains v then none
      else if (match p.head? with | none => true | some h => !com h v) &&
          (p.drop 1).all (fun u => com u v) then extendChain com F n (v :: p)
      else none

@[expose] def chainOf (com : Nat → Nat → Bool) (F : List Nat) (k : Nat) : List Nat :=
  (extendChain com F k []).getD []

@[expose] def mooreWord (P : List Nat) (j : Nat) : List Nat :=
  if j == 1 then [P[0]!, P[1]!] else [P[0]!, P[j]!]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24MooreNative
