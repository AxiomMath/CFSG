module

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.SchreierChainOrderGenerators
public import CFSG.Sporadic.Schreier.PairF2Quad
public import CFSG.Sporadic.Schreier.PairText
public import CFSG.Sporadic.Schreier.PairClasses
public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import CFSG.Sporadic.Schreier.PairF2Quad
public meta import CFSG.Sporadic.Schreier.PairText
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.ImagePairs

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairText CFSG.Sporadic.Schreier.PairF2

@[expose] def j3Monomials : List (ℕ × ℕ) := monomials 80

@[expose] def j3FormsHex : String := include_str "../../../Certificates/Data/CFSGNative/PairSchreier/J3Forms.txt"

@[expose] def j3InvHex : String := include_str "../../../Certificates/Data/CFSGNative/PairSchreier/J3InvForm.txt"

@[expose] def j3InvWord : ℕ := hexAt j3InvHex.toUTF8 0 810

@[expose] def j3StrongHex : String := include_str "../../../Certificates/Data/CFSGNative/PairSchreier/J3Strong.txt"

@[expose] def j3StrongArrs : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 5 => hexTable 4 6156 (6156 * j.val) j3StrongHex

@[expose] def j3StabText : String := include_str "../../../Certificates/Data/CFSGNative/PairSchreier/J3Stab.txt"

@[expose] def j3StabData : List (List ℕ) × List (ℕ × List (ℕ × ℕ × ℕ)) :=
  parseOrbitsMerges (tokens j3StabText)

irreducible_def j3StabOrbits : List (List ℕ) := j3StabData.1

irreducible_def j3Merges : List (ℕ × List (ℕ × ℕ × ℕ)) := j3StabData.2

@[expose] def j3CertOKWith (bytes : ByteArray) (S : Array (Array ℕ)) : Bool :=
  let Sinv := rawInvs 6156 S
  j3Monomials.length == 3240 &&
    (List.range 80).all (fun i => (List.range 80).all fun j =>
      !decide (i ≤ j) || j3Monomials[pairIdx 80 i j]? == some (i, j)) &&
    allLt 6156 (fun r => decide (hexAt bytes (810 * r) 810 < 2 ^ 3240)) &&
    decide (j3InvWord < 2 ^ 3240) && S.size == 5 &&
    allLt 5 (fun j => S[j]!.size == 6156 && isInvA 6156 S[j]! Sinv[j]!) &&
    j3StabOrbits.length == 8 &&
    j3StabOrbits.all (fun o => PairNative.strictInc o && o.all (· < 6156)) &&
    j3StabOrbits.map List.length == [1, 1360, 2040, 1360, 510, 680, 120, 85] &&
    j3Merges.map Prod.fst == [1, 4, 7, 8, 26, 47, 205] &&
    j3Merges.map (fun m => m.2.length) == [6154, 6154, 6154, 6154, 6154, 6154, 6154] &&
    j3Merges.all (fun m => m.2.all fun t => decide (t.1 < 2) && decide (t.2.1 < 6156) &&
      decide (t.2.2 < 6156))

@[expose] def j3CertOK : Bool := j3CertOKWith j3FormsHex.toUTF8 j3StrongArrs

end CFSG.Sporadic.Schreier
