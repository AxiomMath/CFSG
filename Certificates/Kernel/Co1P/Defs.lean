module

public import Certificates.Data.Kernel.Co1P
public import Certificates.Kernel.Co1P.DagData
public import Certificates.Kernel.Co1B.IotaData
public import Certificates.Kernel.Co1Cover.Data
public import CFSG.Sporadic.Co1Block.TwoAData
public import CFSG.Sporadic.Co1Patterson.GraphDataInputs

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KD.Co1B CFSG.KD.Co1P CFSG.KC.Co1P CFSG.KLie.CT
  CFSG.KC.TreeK CertificateChecks.KernelCo1Cover

@[expose] noncomputable def AL : Nat := getL oneK IRS 23

@[expose] noncomputable def gBaseK : List Nat :=
  [R0, R1, getL oneK IRS 23] ++ (List.range 8).map (fun k => getL oneK IRS (36 + k)) ++
    CFSG.Sporadic.Co1Block.twoABray.map fun j => getL oneK BRS59 (j - 1)

@[expose] noncomputable def BK : List Nat :=
  CFSG.Sporadic.Co1Block.twoABray.map fun j => getL oneK BRS59 (j - 1)

@[expose] noncomputable def BIK : List Nat :=
  CFSG.Sporadic.Co1Block.twoABray.map fun j => getL oneK BRIS59 (j - 1)

@[expose] noncomputable def repXK (i : Nat) : Nat :=
  getL oneK GDS (CFSG.Sporadic.Co1Patterson.Native.repIdx.getD i 0 - 1)

@[expose] noncomputable def repXiK (i : Nat) : Nat :=
  getL oneK GDIS (CFSG.Sporadic.Co1Patterson.Native.repIdx.getD i 0 - 1)

@[expose] noncomputable def repK (i : Nat) : Nat := mulWK (mulWK (repXK i) AL) (repXiK i)

@[expose] noncomputable def recsT (ms : List Nat) : List (Nat × Nat) := recsK 8 (masksK 8 64 ms)

@[expose] noncomputable def hsW (ms : List Nat) (i : Nat) : Nat := walkAt (hsAct BK) 8 oneK (recsT ms) i

@[expose] noncomputable def hisW (ms : List Nat) (i : Nat) : Nat :=
  walkAt (hisAct BIK) 8 oneK (recsT ms) i

@[expose] noncomputable def brayTreeOK (ms : List Nat) : Bool :=
  andB (treePts (hsAct BK) 8 oneK (recsT ms)).2 (treePts (hisAct BIK) 8 oneK (recsT ms)).2

end CertificateChecks.KernelCo1P

end
