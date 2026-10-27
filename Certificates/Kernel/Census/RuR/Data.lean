module

public import Certificates.Data.Kernel.Census.PackedBase
public import Certificates.Data.Kernel.Census.PackedTree
public import Certificates.Kernel.SporSch.Ru.Lines
public import Certificates.Kernel.SporSch.Ru.EndR
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 1000000

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.RuR
  "Certificates/Kernel/Census/RuR/data/ruconj.json.gz" 881011 7850599607203245048
  (xs : List Nat) (rs : List Nat) (cjs : List (List Nat)) (bs : List (Nat × Nat)) (us : Array Nat)
  (im : List Nat) (wt : List Nat) (cm : List Nat) (cs : Array Nat) (ci : Array Nat)
  (roots : List (Nat × Nat)) (nodes : Array NodeP) (ents : Array (List (Nat × Nat × Nat)))
  (wcs : Array (Array ArrCertP)) (excs : List ExcRefP) (ps : List Nat) (e0 : Array Nat)
  (O : Nat) (ix : Nat) (li : Array Nat) (xw : List (List Nat))
  (wits : List (Nat × Nat × List (Nat × List Nat × List Nat) × Nat)) (em : List Nat)
  (yw : List Nat)

public section

namespace CertificateChecks.KernelCensus.RuR

open CFSG.KC.Census CertificateChecks.KernelSporSch

@[expose] noncomputable def d : ConjDataP :=
  ⟨xs, rs, cjs, bs, us, im, wt, cm, cs, ci, roots, nodes, ents, wcs, excs⟩

@[expose] noncomputable def cN : Array ArrCertP := pcN 128 7 d.nodes

@[expose] noncomputable def inWP (P : Nat) : Bool := Nat.beq P (pid 128 7)

@[expose] noncomputable def nodeF (i : Nat) : Bool := pnodeOKT 128 7 ps inWP d cN e0 i

@[expose] noncomputable def L (k : Nat) : Nat :=
  bif Nat.blt k 18 then RuT4060.L (Nat.add 15 k) else li[Nat.sub k 18]!

@[expose] def base : List Nat := [0, 1, 2, 3]

@[expose] noncomputable def pe : Array Nat := #[RuT4060.L 0, RuEndR.F 0]

@[expose] noncomputable def witF (t : Nat × Nat × List (Nat × List Nat × List Nat) × Nat) : Bool :=
  (pmem cN[t.1]! (ppcA 128 7 d.xs t.2.1) &&
    t.2.2.1.all (fun f => pmem cN[t.1]! (ppcA 128 7 d.xs f.1))) &&
    witB 12 18 L base xw t.2.1 t.2.2.1 t.2.2.2

end CertificateChecks.KernelCensus.RuR

end
