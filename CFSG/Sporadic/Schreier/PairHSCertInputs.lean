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

@[expose] def hsVectorsHex : String :=
  include_str "../../../Certificates/Data/CFSGNative/PairSchreier/HSVectors.txt"

@[expose] def hsVectors : Array (List ℕ) := hexVectors 3850 20 hsVectorsHex

@[expose] def hsStrongHex : String :=
  include_str "../../../Certificates/Data/CFSGNative/PairSchreier/HSStrong.txt"

@[expose] def hsStrongArrs : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 8 => hexTable 4 3850 (3850 * j.val) hsStrongHex

@[expose] def hsStabText : String := include_str "../../../Certificates/Data/CFSGNative/PairSchreier/HSStab.txt"

@[expose] def hsStabData : List (List ℕ) × List (ℕ × List (ℕ × ℕ × ℕ)) :=
  parseOrbitsMerges (tokens hsStabText)

@[expose] def hsCertOKWith (V : Array (List ℕ)) (S : Array (Array ℕ))
    (st : List (List ℕ) × List (ℕ × List (ℕ × ℕ × ℕ))) : Bool :=
  let Sinv := rawInvs 3850 S
  V.size == 3850 && allLt 3850 (fun i => CFSG.Sporadic.J1.Native.wfV 2 20 V[i]!) &&
    S.size == 8 &&
    allLt 8 (fun j => S[j]!.size == 3850 && isInvA 3850 S[j]! Sinv[j]!) &&
    st.1.length == 12 &&
    st.1.all (fun o => PairNative.strictInc o && o.all (· < 3850)) &&
    st.1.map List.length == [1, 960, 160, 90, 192, 1440, 240, 360, 120, 240, 15, 32] &&
    st.2.map Prod.fst == [1, 3, 4, 6, 7, 8, 36, 41, 93, 128, 158] &&
    st.2.map (fun m => m.2.length) ==
      [3848, 3848, 3848, 3848, 3848, 3848, 3848, 3848, 3848, 3848, 3848] &&
    st.2.all (fun m => m.2.all fun t => decide (t.1 < 2) && decide (t.2.1 < 3850) &&
      decide (t.2.2 < 3850))

@[expose] def hsCertOK : Bool := hsCertOKWith hsVectors hsStrongArrs hsStabData

end CFSG.Sporadic.Schreier
