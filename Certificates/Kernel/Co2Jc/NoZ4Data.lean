module

public import CFSG.Sporadic.Co2Jc.Native.NoZ4
public meta import CFSG.Sporadic.Co2Jc.Native.NoZ4
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Jc.Bits
public meta import CFSG.Sporadic.Co2Jc.Bits
public meta import CFSG.Sporadic.Co2Smith.Cat
public import CFSG.Sporadic.Co2Smith.Cat
import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

namespace CertificateChecks.KernelCo2Jc

open CFSG.Sporadic.Co2Jc.Data

meta def rowM (A i : Nat) : Nat := (A >>> (10 * i)) % 1024

meta def mulM (A B : Nat) : Nat :=
  (List.range 10).foldl (fun acc i =>
    let r := (List.range 10).foldl (fun s k => if (rowM A i).testBit k then s ^^^ rowM B k else s) 0
    acc ||| (r <<< (10 * i))) 0

meta def idM : Nat := (List.range 10).foldl (fun acc i => acc ||| (1 <<< (11 * i))) 0

meta def genM (k : Nat) : Nat :=
  (List.range 10).foldl (fun acc j =>
    let r := (List.range 10).foldl (fun s i =>
      if ((CFSG.Sporadic.Co2Smith.Native.glNJTab[k]!).getD i 0).testBit j then s ||| (1 <<< i) else s) 0
    acc ||| (r <<< (10 * j))) 0

meta def preM (w : List Nat) : Array Nat :=
  ((List.range (w.length + 1)).map fun i => (w.take i).foldl (fun acc k => mulM acc (genM k)) idM).toArray

meta def sufM (w : List Nat) : Array Nat :=
  ((List.range (w.length + 1)).map fun i => (w.drop i).foldr (fun k acc => mulM (genM k) acc) idM).toArray

meta def q4M (w : List Nat) : Array Nat :=
  let P := CFSG.Sporadic.Co2Jc.Native.NoZ4.prod4 w
  (List.range 100).toArray.map fun e => ((P.rows[e / 10]!)[e % 10]!).val

meta def nzArrs : Array (Array Nat) :=
  #[preM (rels[1]!), sufM (rels[1]!), preM (rels[9]!), sufM (rels[9]!)]

meta def nqArrs : Array (Array Nat) := #[q4M (rels[1]!), q4M (rels[9]!)]

end CertificateChecks.KernelCo2Jc

#kc_items CertificateChecks.KernelCo2Jc.NZ include_bytes "data/NoZ4Data.NZ.items" 4016 15145501846579493007
#kc_items CertificateChecks.KernelCo2Jc.NQ include_bytes "data/NoZ4Data.NQ.items" 58 16241666913054577317
