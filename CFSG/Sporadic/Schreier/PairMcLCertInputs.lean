module

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.SchreierChainOrderGenerators
public import CFSG.Sporadic.J1.VecSpec
public import CFSG.Sporadic.Schreier.PairText
public import CFSG.Sporadic.Schreier.PairClasses
public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import CFSG.Sporadic.Schreier.PairText
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.J1.Vec
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.ImagePairs
public import Mathlib

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairText

@[expose] def mclVectorsHex : String :=
  include_str "../../../Certificates/Data/CFSGNative/PairSchreier/McLVectors.txt"

@[expose] def mclVectors : Array (List ℕ) := hexVectors 275 21 mclVectorsHex

@[expose] def mclStrongHex : String :=
  include_str "../../../Certificates/Data/CFSGNative/PairSchreier/McLStrong.txt"

@[expose] def mclStrongArrs : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 13 => hexTable 4 275 (275 * j.val) mclStrongHex

@[expose] def mclStabText : String := include_str "../../../Certificates/Data/CFSGNative/PairSchreier/McLStab.txt"

@[expose] def mclStabData : List (List ℕ) × List (ℕ × List (ℕ × ℕ × ℕ)) :=
  parseOrbitsMerges (tokens mclStabText)

@[expose] def mclCertOKWith (V : Array (List ℕ)) (S : Array (Array ℕ))
    (st : List (List ℕ) × List (ℕ × List (ℕ × ℕ × ℕ))) : Bool :=
  let Sinv := rawInvs 275 S
  V.size == 275 && allLt 275 (fun i => CFSG.Sporadic.J1.Native.wfV 3 21 V[i]!) &&
    S.size == 13 &&
    allLt 13 (fun j => S[j]!.size == 275 && isInvA 275 S[j]! Sinv[j]!) &&
    st.1.length == 3 &&
    st.1.all (fun o => PairNative.strictInc o && o.all (· < 275)) &&
    st.1.map List.length == [1, 112, 162] &&
    st.2.map Prod.fst == [1, 3] &&
    st.2.map (fun m => m.2.length) ==
      [273, 273] &&
    st.2.all (fun m => m.2.all fun t => decide (t.1 < 2) && decide (t.2.1 < 275) &&
      decide (t.2.2 < 275))

@[expose] def mclCertOK : Bool := mclCertOKWith mclVectors mclStrongArrs mclStabData

end CFSG.Sporadic.Schreier
