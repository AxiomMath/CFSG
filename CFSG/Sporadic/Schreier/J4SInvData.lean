module

public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.Schreier.PairText CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.GLQ

@[expose] def invForestText : String :=
  include_str "../../../Certificates/Data/CFSGNative/J4Schreier/inv-forest.txt"

@[expose] def invForest : Array (Array ℕ) := (tokPerms 4 (tokens invForestText) 0 19967).1

@[expose] def fN (j : ℕ) : ℕ := (invForest[j]!)[0]!

@[expose] def fE (j : ℕ) : ℕ := (invForest[j]!)[1]!

@[expose] def fP (j : ℕ) : ℕ := (invForest[j]!)[2]!

@[expose] def fG (j : ℕ) : ℕ := (invForest[j]!)[3]!

@[expose] def invConjText : String :=
  include_str "../../../Certificates/Data/CFSGNative/J4Schreier/inv-conj.txt"

@[expose] def conjTab : Array (Array ℕ) := (tokPerms 1024 (tokens invConjText) 0 4).1

@[expose] def ambText : String :=
  include_str "../../../Certificates/Data/CFSGNative/J4Schreier/inv-ambient.txt"

@[expose] def ambHead : Array (Array ℕ) := (tokPerms 3 (tokens ambText) 0 77).1

@[expose] def ambWordsText : String :=
  include_str "../../../Certificates/Data/CFSGNative/J4Schreier/inv-ambient-words.txt"

@[expose] def ambWords : Array (List ℤ) := (tokWords (tokens ambWordsText) 0 77).1

@[expose] def genInvColumns : Array (Array ℕ) := #[
  #[1, 245, 1674, 885, 497, 162, 1106, 407, 486, 985, 118],
  #[1, 1865, 1668, 1223, 1131, 650, 457, 1037, 486, 1603, 121],
  #[1, 1927, 701, 689, 1659, 1085, 984, 1181, 1309, 1746, 619],
  #[1, 1927, 292, 296, 116, 948, 756, 141, 660, 221, 1124]]

@[expose] def genMapN (g n e : ℕ) : ℕ :=
  if g = 0 then n ^^^ 4 ^^^ app11 elementColumns[e]! 4 else app11 generatorColumns[g - 1]! n

@[expose] def genMapE (g e : ℕ) : ℕ := if g = 0 then e else (conjTab[g - 1]!)[e]!

@[expose] def ambIdx (n e : ℕ) : ℕ :=
  ((List.range 77).find? fun i => (ambHead[i]!)[0]! == n && (ambHead[i]!)[1]! == e).getD 77

@[expose] def forestIdx : Array ℕ := Id.run do
  let mut a := Array.replicate (2048 * 1024) 0
  for j in [0:19967] do
    a := a.set! (fN j + 2048 * fE j) (j + 1)
  return a

@[expose] def hExp : ℕ := 20688908349532

@[expose] def KPairs : Array Pair :=
  #[wordP Xn Yn fiveGenWords[0]!, wordP Xn Yn fiveGenWords[1]!, wordP Xn Yn fiveGenWords[2]!,
    wordP Xn Yn fiveGenWords[3]!]

@[expose] def uPairK (kp : Array Pair) (e : ℕ) : Pair :=
  if _h : 0 < e ∧ (discoveryParents[e]!)[0]! < e then
    mulP (uPairK kp (discoveryParents[e]!)[0]!) kp[(discoveryParents[e]!)[1]!]!
  else oneP
termination_by e
decreasing_by exact _h.2

@[expose] def ambConj (kp : Array Pair) (i : ℕ) : Pair :=
  let w := wordP An Bn ambWords[i]!
  let a := mulP (etaP (ambHead[i]!)[0]!) (uPairK kp (ambHead[i]!)[1]!)
  let h := mulP a (mulP (mulP w (etaP (ambHead[i]!)[2]!)) (invP w))
  mulP (invP w) (powP h hExp)

@[expose] def ambCheck (kp : Array Pair) (i : ℕ) : Bool :=
  let c := ambConj kp i
  let a := mulP (etaP (ambHead[i]!)[0]!) (uPairK kp (ambHead[i]!)[1]!)
  O.eq (mulP (mulP c a) (invP c)).1 (etaP (ambHead[i]!)[2]!).1 &&
    ((ambHead[i]!)[2]! == 1 || (ambHead[i]!)[2]! == 14)

@[noinline, expose] def ambAllOK (kp : Array Pair) : Bool :=
  (List.range 77).all fun i => ambCheck kp i

end CFSG.Sporadic.J4Schreier
