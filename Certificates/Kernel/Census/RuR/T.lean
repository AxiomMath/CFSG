module

public import Certificates.Kernel.Census.RuR.Data
public import CFSG.Certificates.Kernel.Census.ToMainConj
import all Certificates.Kernel.Census.RuR.Data
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.PackedExc
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Census.ToMain
import all CFSG.Certificates.Kernel.Census.ToMainConj
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.RuR

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kCanon : canonC 128 7 d = true := by quickRfl

theorem kE0c : e0.toList.all (canon1 128 7) = true := by quickRfl

theorem kPc : ppcOK 128 7 d.xs d.rs d.cjs d.bs = true := by quickRfl

theorem kInv : pinvOK 128 7 d.xs d.us d.im d.wt = true := by quickRfl

theorem kTab : ptabOK 128 7 d.xs d.cm d.cs d.ci = true := by quickRfl

theorem kRl : Nat.beq d.roots.length d.us.size = true := by quickRfl

theorem kLen : Nat.beq d.xs.length 14 = true := by quickRfl

theorem kNs : Nat.beq d.nodes.size 134 = true := by quickRfl

theorem kPs : ps.all (fun p => Nat.blt p 128) = true := by quickRfl

theorem kE0m : (Nat.beq e0.size 2 && Nat.beq em.length 2 &&
    Nat.beq e0[0]! (ppcA 128 7 d.xs em[0]!) && Nat.beq e0[1]! (ppcA 128 7 d.xs em[1]!)) = true := by
  quickRfl

theorem kR : (d.us.toList.zip d.roots).all
    (fun ur => prootOKC 128 7 (d.nodes.map NodeP.basis) cN d.cs d.ci ur.1 ur.2) = true := by
  quickRfl

end CertificateChecks.KernelCensus.RuR

end
