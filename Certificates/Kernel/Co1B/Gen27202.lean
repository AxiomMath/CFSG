module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PairData
public import CFSG.Assembly.Defs

namespace CertificateChecks.KernelCo1B.Pair27202

open CFSG.KC.Eval CFSG.EvenSporadicStandard.Co1Pair

public meta def wordsV (ws : Array (List Nat)) : Val := .list (ws.map fun w => .list (w.toArray.map .nat))

public meta def numsV (a : Array Nat) : Val := .list (a.map .nat)

public meta def pairStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "pairStep: expected no arguments"
  let a := cpNums
  let e := cpTwRead2.2 + cpN 0 * (7 - cpF 0) + cpN 1 * (7 - cpF 1) + cpN 2 * (7 - cpF 2)
  return #[(`H, numsV (a.extract 0 6)), (`SW, wordsV cpSsRead.1), (`TW0, wordsV (cpTw 0)),
    (`TW1, wordsV (cpTw 1)), (`TW2, wordsV (cpTw 2)), (`D0, numsV (cpDec 0)),
    (`D1, numsV (cpDec 1)), (`D2, numsV (cpDec 2)), (`R, numsV (a.extract e a.size))]

end CertificateChecks.KernelCo1B.Pair27202
