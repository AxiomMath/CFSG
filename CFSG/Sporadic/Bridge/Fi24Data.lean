module

public import Certificates.Data.CFSGNative.Bridge.SurjD
public import Certificates.Data.CFSGNative.Fi24.Certificate

public section

namespace CFSG.Sporadic.Bridge.Fi24

open CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Fi24.Native

set_option compiler.extract_closed false

@[expose] def fi24ImgText : String := include_str "Fi24Images.txt"

@[expose] def fi24SurjText : String := include_str "Fi24Surj.txt"

@[expose] def fi24Spec (rels : List (List (Nat × Bool))) : Spec where
  m := 11
  rels := rels
  imgWords := parseWords fi24ImgText
  surjWords := parseWords fi24SurjText

@[expose] def fi24Check (rels : List (List (Nat × Bool))) : Bool :=
  let O := orbitData ()
  wordChecks nPts (fi24Spec rels) (chainLetters O) O.alpha O.beta

end CFSG.Sporadic.Bridge.Fi24
