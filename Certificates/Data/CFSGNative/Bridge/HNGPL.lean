module

public import Certificates.Data.CFSGNative.Bridge.SurjD
public import Certificates.Data.CFSGNative.HN.Data

public section

namespace CFSG.Sporadic.Bridge.SurjD.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.F5.Native CFSG.Sporadic.Fi23.Native

set_option compiler.extract_closed false

@[expose] def hnRels (_ : Unit := ()) : List (List (Nat × Bool)) := [
    [(0, true), (0, true), (0, true), (0, true)],
    [(0, false), (0, false), (1, false), (0, true), (0, true), (1, true)],
    [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)],
    [(0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true),
      (1, true), (0, true), (1, true), (1, true)],
    [(0, false), (0, false), (0, true), (1, true), (0, true), (1, true), (1, true), (1, true),
      (0, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true),
      (0, true), (1, true), (1, true), (1, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
      (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, false), (1, false), (1, false)],
    [(2, true), (2, true), (0, true), (0, true)],
    [(0, false), (2, false), (0, true), (2, true)],
    [(1, false), (0, false), (1, false), (2, false), (1, true), (0, true), (1, true), (2, true)],
    [(1, true), (0, true), (1, true), (1, true), (1, true), (2, true), (1, true), (0, true),
      (1, true), (1, true), (1, true), (2, true), (1, true), (0, true), (1, true), (1, true),
      (1, true), (2, true)],
    [(3, true), (3, true)],
    [(0, true), (3, true), (0, true), (3, true)],
    [(1, false), (3, false), (1, true), (3, true)],
    [(1, true), (2, false), (1, false), (2, false), (3, true), (2, true), (1, true), (2, true),
      (1, false), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true)],
    [(4, true), (4, true), (4, true), (4, true), (4, true)],
    [(0, false), (4, true), (0, true), (4, true), (4, true)],
    [(2, false), (4, true), (2, true), (4, false), (4, false)],
    [(4, false), (1, false), (4, true), (1, true)],
    [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)]]

@[expose] def hnImgText : String := include_str "HNImages.txt"

@[expose] def hnSurjText : String := include_str "HNSurj.txt"

@[expose] def hnSpec (_ : Unit := ()) : Spec where
  m := 5
  rels := hnRels
  imgWords := parseWords hnImgText
  surjWords := parseWords hnSurjText

@[expose] def hnCheck (_ : Unit) : Bool :=
  let D := CFSG.Sporadic.HN.Native.hnData
  let O := D.orbit ()
  wordChecks D.n hnSpec (slpLetters D.n (genT D.n O) D.words) O.alpha O.beta

end CFSG.Sporadic.Bridge.SurjD.Native
