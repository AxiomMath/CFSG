module

public import Certificates.Data.CFSGNative.J4.Cert
public import Certificates.Data.CFSGNative.Bridge.SurjD

public section

namespace CFSG.Sporadic.Bridge.J4.Native

open CFSG.Sporadic.J4.Native CFSG.Sporadic.Bridge.SurjD.Native

set_option compiler.extract_closed false

@[expose] def letterOfZ (l : Nat × Bool) : Int :=
  if l.2 then (l.1 : Int) + 1 else -((l.1 : Int) + 1)

@[expose] def imgText : String := include_str "J4Images.txt"

@[expose] def stdText : String := include_str "J4Std.txt"

@[expose] def conjText : String := include_str "J4Conj.txt"

@[expose] def conjInvText : String := include_str "J4ConjInv.txt"

@[expose] def imgWords : List (List Int) := (parseWords imgText).toList

@[expose] def stdWords : List (List Int) := (parseWords stdText).toList

@[expose] def conjRowsG : Array V2 := rowsOf conjText

@[expose] def conjInvRowsG : Array V2 := rowsOf conjInvText

@[noinline, expose] def imageChecks (rels : List (List Int)) (I Iv : Array (Array V2)) : Bool :=
  I.size == 3 && invsOK I Iv && rels.all (fun r => eqRows (wordRows I Iv r) idRows) &&
    stdWords.length == 2 &&
    eqRows (mulRows rowsA conjRowsG)
      (mulRows conjRowsG (wordRows I Iv (stdWords[0]?.getD []))) &&
    eqRows (mulRows rowsB conjRowsG)
      (mulRows conjRowsG (wordRows I Iv (stdWords[1]?.getD []))) &&
    eqRows (mulRows conjRowsG conjInvRowsG) idRows

@[noinline, expose] def inverseChecks (rels : List (List Int)) (I : Array (Array V2)) : Bool :=
  imageChecks rels I (I.map invRows)

@[expose] def j4Check (rels : List (List Int)) : Bool :=
  inverseChecks rels (imgWords.toArray.map (wordRows baseMats baseInvs))

end CFSG.Sporadic.Bridge.J4.Native
