module

public import Certificates.Kernel.Co1B.Data27202
public import Certificates.Kernel.Co1B.Dag27202
public import Certificates.Kernel.Co1B.Text27202
public import Certificates.Kernel.Co1B.Data27207
public import Certificates.Data.Kernel.Co1BPair
public import Certificates.Data.Kernel.Co1BSpin
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Pair27202

open CFSG.KC.Co1BPair CFSG.KC.Co1BSpin CFSG.KC.Co1B

@[expose] noncomputable def G7 : List Nat := (List.range 7).map P.M

theorem kNums : leqK (numsOf PT.chars) (T.H ++ encW T.SW ++ encW T.TW0 ++ encW T.TW1 ++ encW T.TW2 ++
    T.D0 ++ T.D1 ++ T.D2 ++ T.R) = true := by quickRfl
theorem kGood : (PT.chars.splitOn ' ').all goodP = true := by quickRfl
theorem kLen : (Nat.beq T.H.length 6 && Nat.beq T.SW.length 5 && Nat.beq T.TW0.length 1365 &&
    Nat.beq T.TW1.length 1024 && Nat.beq T.TW2.length 180 && Nat.beq T.D0.length 9555 &&
    Nat.beq T.D1.length 5120 && Nat.beq T.D2.length 540 && T.TW0.head? == some [] &&
    T.TW1.head? == some [] && T.TW2.head? == some []) = true := by quickRfl
theorem kX : eqK (P.M 0) Cent27207.K.X = true := by quickRfl
theorem kY : eqK (P.M 1) Cent27207.K.Y = true := by quickRfl
theorem kS : wordsK P.M [P.M 0, P.M 1] 0 2 2 T.SW 0 = true := by quickRfl
theorem kT0 : wordsK P.M G7 0 7 7 T.TW0 0 = true := by quickRfl
theorem kT1 : wordsK P.M G7 2 7 1372 T.TW1 0 = true := by quickRfl
theorem kT2 : wordsK P.M G7 4 7 2396 T.TW2 0 = true := by quickRfl
theorem kL0 : levK P.M 0 T.D0 0 = true := by quickRfl
theorem kL1 : levK P.M 1 T.D1 0 = true := by quickRfl
theorem kL2 : levK P.M 2 T.D2 0 = true := by quickRfl

end CertificateChecks.KernelCo1B.Pair27202

end
