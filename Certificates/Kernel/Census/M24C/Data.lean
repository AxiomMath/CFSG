module

public import Certificates.Data.Kernel.Census.PackedConj
public import Certificates.Data.Kernel.Census.PackedExc
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.M24C
  "Certificates/Kernel/Census/M24C/data/m24conj.json.gz" 255165 15543777627439946855
  (xs : List Nat) (rs : List Nat) (cjs : List (List Nat)) (bs : List (Nat × Nat)) (us : Array Nat)
  (im : List Nat) (wt : List Nat) (cm : List Nat) (cs : Array Nat) (ci : Array Nat)
  (roots : List (Nat × Nat)) (nodes : Array NodeP) (ents : Array (List (Nat × Nat × Nat)))
  (wcs : Array (Array ArrCertP)) (excs : List ExcRefP) (xg : Array Nat) (Xs : Array Nat)
  (xw : List (List Nat)) (e0 : Array Nat) (e0wit : WitP)
  (e0cl : List (List Nat) × List (Nat × Nat) × List (List Nat) × List Nat)

public section

namespace CertificateChecks.KernelCensus.M24C

open CFSG.KC.Census

@[expose] noncomputable def d : ConjDataP :=
  ⟨xs, rs, cjs, bs, us, im, wt, cm, cs, ci, roots, nodes, ents, wcs, excs⟩

@[expose] noncomputable def inXP : Nat → Bool := pinXL Xs

@[expose] noncomputable def cN : Array ArrCertP := pcN 24 5 d.nodes

@[expose] noncomputable def nodeF (i : Nat) : Bool :=
  pnodeOKC 24 5 [0, 1, 2, 3, 4, 5, 8, 9] inXP (fun _ => true) inXP true false false d cN e0 i

end CertificateChecks.KernelCensus.M24C

end
