module

public import Certificates.Data.Kernel.Census.PackedConjF
import all Certificates.Data.Kernel.Census.Packed
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.J3
  "Certificates/Kernel/Census/J3/data/j3.json.gz" 31999286 6471677107238551011
  (j3Xs : List Nat) (j3Rs : List Nat) (j3Cjs : List (List Nat)) (j3Bs : List (Nat × Nat))
  (j3Im : List Nat) (j3Wt : List Nat) (j3Roots : List (Nat × Nat))
  (j3Bases : Array (Array Nat)) (j3Ents : Array (List (Nat × Nat × Nat)))
  (j3EL : List (Nat × Nat × Nat)) (j3Us : Array Nat) (j3Cs : Array Nat) (j3Wits : Array WitP)
  (j3Aux : Array (Nat × Nat)) (j3Si : Array Nat) (j3XE : Array Nat) (j3XW : List (List Nat))

public section

namespace CertificateChecks.KernelCensus.J3

open CFSG.KC.Census

@[expose] noncomputable def j3Nodes : Array NodeP :=
  Array.mk ((j3Bases.toList.zip j3Wits.toList).map fun bw => ⟨bw.1, bw.2, #[]⟩)

@[expose] noncomputable def j3Conj : ConjDataP :=
  ⟨j3Xs, j3Rs, j3Cjs, j3Bs, j3Us, j3Im, j3Wt, [0], j3Cs, j3Cs, j3Roots, j3Nodes, j3Ents, #[], []⟩

@[expose] noncomputable def psL : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

@[expose] noncomputable def cNL : Array ArrCertP :=
  Array.mk (j3Bases.toList.map fun b => pmaskCert 6156 13 b)

@[expose] noncomputable def entB (i a L : Nat) : Bool :=
  (((j3Us.toList.drop a).take L).zip ((j3Ents[i]!.drop a).take L)).all fun ue =>
    pentOK 6156 13 j3Bases cNL j3Cs j3Cs i ue.1 ue.2

@[expose] noncomputable def j3EB : List (Nat × Nat × Nat) :=
  j3EL.flatMap fun t => (List.range t.2.2).map fun c => (t.1, c * t.2.1, t.2.1)

@[expose] noncomputable def ebF (b : Nat × Nat × Nat) : Bool := entB b.1 b.2.1 b.2.2

@[expose] noncomputable def inXP (P : Nat) : Bool := pinXL j3XE P

@[expose] noncomputable def nodeF (i : Nat) : Bool :=
  penumF 6156 13 j3Bases[i]! psL &&
    pwitF 6156 13 psL inXP (fun _ => true) false false false j3Bases[i]! cNL[i]! j3Conj.wcs[i]!
      j3Aux[i]! j3Conj.nodes[i]!.wit

@[expose] noncomputable def usF (c : Nat) : Bool :=
  (((j3Us.toList.drop (c * 5)).take 5).zip ((j3Im.drop (c * 5)).take 5)).all
    fun ua => Nat.beq (ppcA 6156 13 j3Xs ua.2) ua.1

@[expose] noncomputable def headF (k : Nat) : Bool :=
  ppcHeadAt 6156 13 (j3Xs.drop k) (j3Rs.drop k) (j3Cjs.drop k) (j3Bs.drop k)

end CertificateChecks.KernelCensus.J3

end
