module

public import Certificates.Kernel.Census.J3.Data
import all Certificates.Kernel.Census.J3.Data
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedConj
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.J3

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kWalk : pinvRest 6156 13 j3Xs 0 j3Im j3Wt = some [] := by decide +kernel

theorem kInvL : (Nat.beq j3Im.length j3Us.size && Nat.beq j3Wt.length (2 ^ j3Xs.length)) =
    true := by
  quickRfl

theorem kTab : ptabOK 6156 13 j3Xs [0] j3Cs j3Cs = true := by quickRfl

theorem kRoots : ((j3Us.toList.zip j3Roots).all fun ur =>
    prootOKC 6156 13 j3Bases cNL j3Cs j3Cs ur.1 ur.2) = true := by
  quickRfl

theorem kRL : Nat.beq j3Roots.length j3Us.size = true := by quickRfl

theorem kBM : (j3Bases.toList.all fun b => b.toList.all fun x => j3Us.toList.any (Nat.beq x)) =
    true := by
  quickRfl

theorem kEL : (j3EL.all fun t => Nat.beq j3Ents[t.1]!.length j3Us.size &&
    Nat.ble j3Us.size (t.2.2 * t.2.1)) = true := by
  quickRfl

theorem kMono : (List.range 208).all (fun i =>
    j3Conj.nodes[i]!.wit.isMono || j3EL.any (fun t => t.1 == i)) = true := by
  quickRfl

theorem kNS : (Nat.beq j3Conj.nodes.size 208 && Nat.beq j3Bases.size 208 &&
    Nat.beq j3Wits.size 208 && Nat.beq j3Aux.size 208) = true := by
  quickRfl

theorem kXsL : Nat.beq j3Xs.length 8 = true := by quickRfl

theorem kXES : Nat.beq j3XE.size 300 = true := by quickRfl

theorem kEBL : Nat.beq j3EB.length 62 = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
