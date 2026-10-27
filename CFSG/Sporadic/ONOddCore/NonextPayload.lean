module

public import CFSG.Sporadic.ONOddCore.LocalAutPayload

public section

namespace CFSG.Sporadic.ONOddCore

structure ExclRec where
  index : Nat
  normWord : List Nat
  second : Nat
  conjWord : List Nat
deriving Inhabited

structure InnerRec where
  index : Nat
  conjWord : List Nat
deriving Inhabited

structure NonextCert where
  relationWord : List Nat
  excluded : List ExclRec
  inner : List InnerRec
deriving Inhabited

structure NonextWords where
  tWord : List Nat
  dWords : List (List Nat)
  dcWords : List (List Nat)
  vWord : List Nat
deriving Inhabited

@[expose] def nonextCert : NonextCert where
  relationWord := [2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5,
    2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5]
  excluded := [
    ⟨2, [2, 3, 2, 2, 2, 2, 3, 2, 2, 2, 3, 2, 3, 1],
      2, [3, 3, 3, 2, 2, 3, 3, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3]⟩,
    ⟨3, [3, 3, 3, 3, 2, 2, 3, 2, 3],
      2, [3, 3, 3, 2, 2, 3, 3, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3]⟩,
    ⟨4, [2, 2, 2, 3, 2, 3, 2, 2, 2],
      2, [2, 3, 2, 2, 3, 2, 2, 2, 3, 3, 2, 3, 2]⟩,
    ⟨6, [3, 3, 3, 2, 2, 2, 2, 3, 3, 3, 1],
      2, [2, 3, 2, 2, 3, 2, 2, 2, 3, 3, 2, 3, 2]⟩,
    ⟨9, [3, 3, 3, 3, 3, 3, 2, 3, 3],
      9, [3, 2, 2, 2, 3, 2, 3, 2, 3, 3, 3, 2, 3, 3, 2]⟩,
    ⟨10, [3, 2, 3, 2, 2, 2, 2, 3, 2, 3, 2, 3, 3],
      9, [3, 2, 2, 2, 3, 2, 3, 2, 3, 3, 3, 2, 3, 3, 2]⟩,
    ⟨12, [3, 3, 2, 2, 2, 2, 2, 3, 2, 2],
      9, [2, 2, 3, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 3, 3, 2]⟩,
    ⟨13, [3, 2, 2, 2, 2, 2, 2, 3, 2, 3, 2],
      9, [2, 2, 3, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 3, 3, 2]⟩]
  inner := [
    ⟨0, []⟩,
    ⟨1, [3, 3, 3, 3, 2, 3, 2, 2, 2, 2, 3, 2]⟩,
    ⟨5, [2, 3, 2, 3, 3, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 3, 1]⟩,
    ⟨7, [2, 2, 2, 3, 2, 3, 2, 3, 2, 2, 2, 3, 3, 2, 2]⟩]

@[expose] def nonextWords : NonextWords where
  tWord := [3, 3, 2, 2, 3, 3, 3, 3, 3, 2, 3, 3, 2, 2, 2, 2]
  dWords := [
    [3, 3, 2, 2, 3, 3, 3, 3, 3, 2, 3, 3, 2, 2, 2, 2],
    [3, 3, 3, 2, 2, 2, 3, 2, 2, 2, 3, 2, 2, 3, 2],
    [3, 3, 2, 2, 3, 3, 2, 2, 2, 3, 2, 2, 2, 3, 3, 3],
    [2, 3, 3, 3, 3, 2, 2, 3, 2, 2, 2]]
  dcWords := [
    [1],
    [2, 3, 3, 3, 2, 2, 3, 2, 2, 3, 3, 3, 2, 2, 2, 2, 2, 1],
    [2, 2, 2, 3, 3, 2, 3, 3, 2, 1],
    [3, 3, 3, 2, 2, 3, 2, 2, 2, 2, 2, 2, 3, 3, 2, 2, 1]]
  vWord := [2, 2, 2, 2, 3, 3, 3, 2, 2, 3, 2, 2, 3, 3, 3, 2, 2]

@[expose] def flatLifts : List LiftEntry := localCert.records.flatMap QuotRecord.lifts

end CFSG.Sporadic.ONOddCore
