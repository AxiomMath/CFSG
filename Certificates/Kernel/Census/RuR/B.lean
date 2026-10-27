module

public import Certificates.Kernel.Census.RuR.Data
import all Certificates.Kernel.Census.RuR.Data
import all Certificates.Data.Kernel.Census.PackedBase
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.RuR

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kInvL : invLB 12 18 L 4060 = true := by quickRfl

theorem kPts : (List.range 128).all (fun q => Nat.blt (at' 12 O q) 4060 &&
    Nat.beq (at' 7 ix (at' 12 O q)) q) = true := by quickRfl

theorem kXl : Nat.beq xw.length 14 = true := by quickRfl

theorem kXw : xw.all (fun x => x.all fun k => Nat.blt k 36) = true := by quickRfl

theorem kRel : pcRelB 12 L base xw d.rs d.cjs = true := by quickRfl

theorem kRes : (xw.zip d.xs).all (fun p => resB 12 L 7 128 O ix p.1 p.2) = true := by quickRfl

theorem kCov : (List.range d.nodes.size).all (fun i => !d.nodes[i]!.wit.isMono ||
    wits.any fun t => Nat.beq t.1 i) = true := by quickRfl

theorem kWl : wits.all (fun t => t.2.2.1.all fun f =>
    f.2.1.all (fun k => Nat.blt k 36) && f.2.2.all (fun k => Nat.blt k 36)) = true := by quickRfl

theorem kWi : wits.all (fun t => Nat.blt t.1 d.nodes.size) = true := by quickRfl

theorem kWit : wits.all witF = true := by quickRfl

theorem kYw : yw.all (fun k => Nat.blt k 36) = true := by quickRfl

theorem kPe : (List.range 4060).all (fun b => Nat.blt (at' 12 pe[0]! b) 4060 &&
    Nat.blt (at' 12 pe[1]! b) 4060) = true := by quickRfl

theorem kE0 : (conjB 12 L (List.range 4060) xw em[0]! yw pe[0]! &&
    conjB 12 L (List.range 4060) xw em[1]! yw pe[1]!) = true := by quickRfl

end CertificateChecks.KernelCensus.RuR

end
