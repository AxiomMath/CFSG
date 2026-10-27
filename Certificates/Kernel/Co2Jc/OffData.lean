module

public import CFSG.Sporadic.Co2Jc.Native.Offenders
public meta import CFSG.Sporadic.Co2Jc.Native.Offenders
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat
public meta import CFSG.Sporadic.Co2Smith.Cat
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2Jc

open CFSG.Sporadic.Co2Jc.Native

meta def packTab (l : List Nat) : Nat :=
  (List.range 10).foldl (fun acc c => acc ||| (l.getD c 0 <<< (10 * c))) 0

meta def tabsA : Array (List Nat) := tabs.toArray

meta def keysA : Array Nat := tabsA.map enc

meta def idxOfTab (l : List Nat) : Nat := (keysA.findIdx? (· == enc l)).getD 256

meta def mulA : Array (Array Nat) :=
  (Array.range 256).map fun s => (Array.range 256).map fun i =>
    idxOfTab (compL (tabsA[s]!) (tabsA[i]!))

meta def gensA : Array (List Nat) := gens.toArray

meta def parentOf (i : Nat) : Nat × Nat := Id.run do
  for p in [0:i] do
    for k in [0:4] do
      if tabsA[i]! == compL (gensA[k]!) (tabsA[p]!) then return (p, k)
  return (0, 0)

meta def subsA : Array (List Nat) := subs.toArray

meta def offIdx : Array (Array Nat) :=
  let par := (Array.range 256).map parentOf
  #[par.map (·.1), par.map (·.2), gensA.map idxOfTab]

meta def offTabs : Array (Array Nat) := tabsA.map fun l => #[packTab l]

meta def offFix : Array (Array Nat) :=
  tabsA.map fun l => #[(List.range 1024).foldl (fun acc m =>
    if CFSG.Sporadic.Co2Jc.colAct (tabF l) m == m then acc ||| (1 <<< m) else acc) 0]

meta def subIdx (l : List Nat) : Nat := (subsA.findIdx? (· == l)).getD 1023

meta def offStep : Array (Array Nat) :=
  let M := mulA
  subsA.map fun l => (Array.range 256).map fun s =>
    let mm := fun (a b : Nat) => (M[a]!)[b]!
    if l.contains s || s == 0 || mm s s != 0 || !(l.all fun i => mm s i == mm i s) then 1023
    else subIdx ((List.range 256).filter fun i => l.contains i || (l.map (mm s)).contains i)

end CertificateChecks.KernelCo2Jc

#kmisc_packarrs CertificateChecks.KernelCo2Jc.OP CertificateChecks.KernelCo2Jc.offTabs 100
#kmisc_packarrs CertificateChecks.KernelCo2Jc.OM CertificateChecks.KernelCo2Jc.mulA 10
#kmisc_packarrs CertificateChecks.KernelCo2Jc.OI CertificateChecks.KernelCo2Jc.offIdx 10
#kmisc_packarrs CertificateChecks.KernelCo2Jc.OF CertificateChecks.KernelCo2Jc.offFix 1024
#kmisc_packarrs CertificateChecks.KernelCo2Jc.OS CertificateChecks.KernelCo2Jc.offStep 10
