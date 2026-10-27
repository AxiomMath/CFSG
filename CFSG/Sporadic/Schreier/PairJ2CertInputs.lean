module

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.SchreierChainOrderGenerators
public import CFSG.Sporadic.J1.VecSpec
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.Sporadic.Schreier.PairText
public import Certificates.Data.CFSGNative.PairSchreier.J2Data
public meta import CFSG.Sporadic.Schreier.PairText
public meta import Certificates.Data.CFSGNative.PairSchreier.J2Data
public meta import Certificates.Data.CFSGNative.J1.Vec
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import Mathlib

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairText

@[expose] def j2VectorsHex : String := include_str "../../../Certificates/Data/CFSGNative/PairSchreier/J2Vectors.txt"

@[expose] def j2Vectors : Array (List ℕ) := hexVectors 315 14 j2VectorsHex

@[expose] def j2SylowsText : String := include_str "../../../Certificates/Data/CFSGNative/PairSchreier/J2Sylows.txt"

@[expose] def j2Sylows : Array SylowRec := parseSylows 315 (tokens j2SylowsText)

@[expose] def j2PermOK (t : Array ℕ) : Bool := t.size == 315 && isInvA 315 t (invCand 315 t)

@[expose] def j2RecordOK (r : NGRec) : Bool :=
  j2PermOK r.rep &&
    r.conj.all (fun w => w.all fun l => l == 1 || l == -1 || l == 2 || l == -2) &&
    decide (r.chain.gens.size ≤ r.chain.strong.size) &&
    r.chain.base.all (· < 315) && decide r.chain.base.Nodup &&
    r.chain.strong.all j2PermOK &&
    (List.range r.chain.gens.size).all (fun k => r.chain.gens[k]! == r.chain.strong[k]!) &&
    r.chain.words.size + r.chain.gens.size == r.chain.strong.size

@[expose] def j2CertOK : Bool :=
  j2Vectors.size == 315 && allLt 315 (fun i => CFSG.Sporadic.J1.Native.wfV 5 14 j2Vectors[i]!) &&
    j2StrongArrs.size == 7 && allLt 7 (fun j => j2PermOK j2StrongArrs[j]!) &&
    allLt 7 (fun j => isInvA 315 j2StrongArrs[j]! (rawInvs 315 j2StrongArrs)[j]!) &&
    j2Words.size == 7 &&
    (j2Sylows.toList.map fun e => e.prime) == [2, 3, 5, 7] &&
    (j2Sylows.toList.map fun e => e.gens.size) == [7, 3, 2, 1] &&
    (j2Sylows.toList.map fun e => e.records.size) == [35, 13, 6, 1] &&
    j2Sylows.all (fun e => e.gens.all j2PermOK && e.records.all j2RecordOK)

end CFSG.Sporadic.Schreier
