module

public import Certificates.Data.PairOrbit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveInputs
public meta import Certificates.Data.PairOrbit
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveInputs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Fi24PairSize

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveNative
  CFSG.HardMathSupport.Solomon.Coordinator.PtOrbit CFSG.HardMathSupport.Solomon.Coordinator.PairOrbit

set_option compiler.extract_closed false

@[expose] def pairText : String :=
  "0410100802060604060604060606060606040A0808080A0A080A0A08080A0A080A080E0C0C0E0E0E0E0E0C0C0E0C0E0E0E0E\
  0D0D110C0C110D1815|14190C17100C0F0F0F0D0D0F0D0F0F0F0F090909090909090B090B0B0B090B090B090B0B070707050\
  5070507070507050705070707050700050B09150D|18150C19130D0F0F0F0F0D0D0D0F0D0F0F0D0F0D0D0F09090909090909\
  0B090909090B0B09090B0B090B0B040705050707070707050705050707070507050705000513150503|14190C17130C0F0D0\
  F0D0F0D0D0D0F0D0D0F0F0F0D0909090909090909090909090909090B09090B090B0B090B090B0B040707050507070705050\
  70707070507000F07170B|18150D13190C0F0D0D0F0D0F0D0D0D0F0F0F0F0D0D0D0808080B0909090B0B090B09090B090905\
  070507070507050707070507070705031507031307|18150C19100D0F0D0F0D0F0F0F0F0D0F0D0F0D0F0D0D0909090909090\
  90B090B0909090B0B0B0B09090B0905070505070507050707050705070705070700050913030F"

@[expose] def hexVal (c : Char) : Nat := if 65 ≤ c.toNat then c.toNat - 55 else c.toNat - 48

@[expose] def parseHex : List Char → List Nat
  | a :: b :: r => (hexVal a * 16 + hexVal b) :: parseHex r
  | _ => []

@[expose] def pairWords (_ : Unit := ()) : List (List Nat) :=
  (pairText.splitOn "|").map fun w => parseHex w.toList

@[expose] def fixCnt (T : Table) : Nat := (List.range 306936).countP fun i => ap T i == i

@[expose] def pairOK24 (c : Ctx) (S : Table) (wa wb : List Nat) (c0 cap : Nat) : Bool :=
  let A := wordTab c wa
  let B := wordTab c wb
  let G : Array Table := #[A, B]
  let T := pairBFS 306936 G c0 cap
  wa.all (fun z => decide (z < 26)) && wb.all (fun z => decide (z < 26)) &&
    eqTab24 (powT 306936 7 A) (idT 306936) && !eqTab24 A (idT 306936) &&
    eqTab24 (powT 306936 7 B) (idT 306936) && !eqTab24 B (idT 306936) &&
    eqTab24 (compT 306936 A S) (compT 306936 S A) && eqTab24 (compT 306936 B S) (compT 306936 S B) &&
    decide (c0 < 306936 * 306936) && pairOK 306936 G c0 T && decide (81 ∣ T.pts.size)

@[expose] def fi24PairOK (O : Enum) : Bool :=
  let c := mkCtx O
  let ws := pairWords ()
  decide (ws.length = 6) &&
    decide (fixCnt (wordTab c [18]) = 3240) && decide (fixCnt (wordTab c [16, 19]) = 1485) &&
    decide (fixCnt (wordTab c [14, 16, 16, 14, 16, 16]) = 378) &&
    decide (fixCnt (wordTab c [16]) = 162) && decide (fixCnt (wordTab c [2]) = 0) &&
    pairOK24 c (wordTab c [18]) (ws.getD 0 []) (ws.getD 1 []) 2455496 20000 &&
    pairOK24 c (wordTab c [14, 16, 16, 14, 16, 16]) (ws.getD 2 []) (ws.getD 3 []) 613874 300000 &&
    pairOK24 c (wordTab c [2]) (ws.getD 4 []) (ws.getD 5 []) 3799 1000000

end CFSG.HardMathSupport.Solomon.Coordinator.Fi24PairSize
