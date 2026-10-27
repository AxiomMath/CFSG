module

public import Certificates.Data.Kernel.Census.PackedConj
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.HSC
  "Certificates/Kernel/Census/HSC/data/hsconj.json.gz" 247722 9046850992923576248
  (xs : List Nat) (rs : List Nat) (cjs : List (List Nat)) (bs : List (Nat × Nat)) (us : Array Nat)
  (im : List Nat) (wt : List Nat) (cm : List Nat) (cs : Array Nat) (ci : Array Nat)
  (roots : List (Nat × Nat)) (nodes : Array NodeP) (ents : Array (List (Nat × Nat × Nat)))
  (Xs : Array Nat)

public section

namespace CertificateChecks.KernelCensus.HSC

open CFSG.KC.Census

@[expose] noncomputable def d : ConjDataP := ⟨xs, rs, cjs, bs, us, im, wt, cm, cs, ci, roots, nodes, ents, #[], []⟩

@[expose] noncomputable def inXP : Nat → Bool := pinXL Xs

@[expose] noncomputable def inWP : Nat → Bool := pinXL xs.toArray

@[expose] noncomputable def cN : Array ArrCertP := pcN 100 7 d.nodes

@[expose] noncomputable def nodeF (i : Nat) : Bool :=
  pnodeOKC 100 7 [0, 1, 2, 3, 4] inXP (fun _ => true) inWP false false false d cN #[] i

end CertificateChecks.KernelCensus.HSC

end
