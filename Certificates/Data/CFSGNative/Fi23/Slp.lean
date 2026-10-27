module

public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.Sporadic.Fi23.Native

open CFSG.Sporadic.Th.Native

@[inline, expose] def slpLetterT (gens : Int → Table) (L : Array Table) (z : Int) : Table :=
  if z.natAbs ≤ 2 then gens z
  else if 0 < z then L[2 * (z.natAbs - 3)]! else L[2 * (z.natAbs - 3) + 1]!

@[expose] def slpLetters (n : Nat) (gens : Int → Table) (words : Array (List Int)) :
    Array Table :=
  words.foldl (fun L w => let T := wordT n (slpLetterT gens L) w; (L.push T).push (invT n T)) #[]

@[expose] def slpOK (words : Array (List Int)) : Bool :=
  allIn 0 words.size fun j => words[j]!.all fun z => z != 0 && (z.natAbs ≤ 2 || z.natAbs < j + 3)

@[expose] def slpPure (words : Array (List Int)) : Bool :=
  allIn 2 words.size fun j => words[j]!.all fun z => 3 ≤ z.natAbs

end CFSG.Sporadic.Fi23.Native
