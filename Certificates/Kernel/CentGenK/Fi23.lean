module

public import Certificates.Data.Kernel.SlpRel
public import Certificates.Kernel.Fi23M.Data
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CertificateChecks.KernelCentGenK.Fi23
  "Certificates/Kernel/CentGenK/data/fi23cg.json.gz" 7758 12821814296926681558
  (pa : List (List Nat)) (pb : List (List Nat)) (ie : Nat) (jf : Nat) (is1 : Nat) (is2 : Nat)
  (r1 : Nat) (ra : Nat) (rb : Nat)

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCentGenK.Fi23

open CFSG.KC.Enum CFSG.KC.SlpRel CFSG.KD.Fi23M

@[expose] noncomputable def fiNeOne (one X : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true false (Nat.beq X one)

@[expose] noncomputable def fiCgK (prog : List (List Nat)) (ps : List (List Nat × List Nat))
    (ne : List Nat) : Bool :=
  strictB LO fun lo => strictB CI fun ci => strictB RM fun rm => strictB ONE fun one =>
  strictB (MT (nat_lit 0)) fun a => strictB (MT (nat_lit 1)) fun b =>
    slpRelK strictB (CFSG.KC.Ord.mul3s (nat_lit 253) (nat_lit 64009) lo ci rm) one Nat.beq
      (fiNeOne one) [a, b] prog ps ne

@[expose] noncomputable def prog : List (List Nat) := List.append pa pb

@[expose] noncomputable def ps : List (List Nat × List Nat) :=
  [([ie, ie, ie, ie, ie], []), ([jf, jf, jf, jf, jf], []), ([ie, jf], [jf, ie]),
   ([is1, ie], [ie, is1]), ([is2, jf], [jf, is2]), ([r1], [jf, ie]),
   ([Nat.add r1 1], [r1, ie]), ([Nat.add r1 2], [Nat.add r1 1, ie]),
   ([Nat.add r1 3], [Nat.add r1 2, ie]), ([ra], [1]), ([rb], [2])]

@[expose] noncomputable def ne : List Nat :=
  [ie, jf, r1, Nat.add r1 1, Nat.add r1 2, Nat.add r1 3]

set_option Elab.async false

theorem ch17254_ok : fiCgK prog ps ne = true := by
  quickRfl

example : fiCgK [[1, 1]] [([3], [])] [1, 2] = true := by decide +kernel

example : fiCgK [[1, 2]] [([3], [])] [] = false := by decide +kernel

example : fiCgK [] [([1, 2], [2, 1])] [] = false := by decide +kernel

example : fiCgK [[]] [] [3] = false := by decide +kernel

example : fiCgK [[1, 1]] [] [3] = false := by decide +kernel

end CertificateChecks.KernelCentGenK.Fi23

end
