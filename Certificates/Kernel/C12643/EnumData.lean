module

public import Certificates.Kernel.C12643.Elts
public import Certificates.Kernel.Misc.Perm.J2EnumData
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4Data

#kc_repo #kc_json_gz CertificateChecks.KernelC12643 "Certificates/Kernel/C12643/data/c12643enum.json.gz" 591058 9849720219205952961
  (C5aP : List Nat) (C5aE : List Nat) (C5aR : List Nat) (C5aL : List Nat)
  (C5cP : List Nat) (C5cE : List Nat) (C5cR : List Nat) (C5cL : List Nat)
  (C7P : List Nat) (C7E : List Nat) (C7R : List Nat) (C7L : List Nat)
  (CEP : List Nat) (CEE : List Nat) (CER : List Nat) (CEL : List Nat)
  (DP : List Nat) (DE : List Nat) (DR : List Nat) (DL : List Nat)
  (S5P : List Nat) (S5E : List Nat) (S5R : List Nat) (S5L : List Nat)

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelC12643.GC5A
  CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.gC5a 9
#kmisc_packarrs CertificateChecks.KernelC12643.GC5C
  CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.gC5c 9
#kmisc_packarrs CertificateChecks.KernelC12643.GCEP
  CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.gCE 9
#kmisc_packarrs CertificateChecks.KernelC12643.GDP
  CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.gD 9
#kmisc_packarrs CertificateChecks.KernelC12643.LNP
  CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.lineA 9
#kmisc_packarrs CertificateChecks.KernelC12643.TRP
  CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.transA 9
#kmisc_packarrs CertificateChecks.KernelC12643.DUP
  CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.dUA 9
#kmisc_packarrs CertificateChecks.KernelC12643.DVP
  CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.dVA 9

public section

namespace CertificateChecks.KernelC12643

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CertificateChecks.KernelMisc.J2C3 (keyF chunkK)
open CertificateChecks.KernelMisc.J2En (certL EL)

@[expose] noncomputable def c5aL : CFSG.Monster.B.Fischer.ArrCert := certL 300 2 C5aP C5aE C5aR C5aL
@[expose] noncomputable def c5cL : CFSG.Monster.B.Fischer.ArrCert := certL 50 2 C5cP C5cE C5cR C5cL
@[expose] noncomputable def c7L : CFSG.Monster.B.Fischer.ArrCert := certL 7 1 C7P C7E C7R C7L
@[expose] noncomputable def cEL : CFSG.Monster.B.Fischer.ArrCert := certL 240 2 CEP CEE CER CEL
@[expose] noncomputable def cDL : CFSG.Monster.B.Fischer.ArrCert := certL 60 2 DP DE DR DL
@[expose] noncomputable def cS5L : CFSG.Monster.B.Fischer.ArrCert := certL 25 2 S5P S5E S5R S5L

@[expose] noncomputable def G7 : ℕ → ℕ := lget [X7]
@[expose] noncomputable def GS5 : ℕ → ℕ := lget [X5A, Y2]

@[expose] noncomputable def c12643pt5a : ℕ → Bool :=
  chunkK 60 (pointK 315 9 2 300 GC5A (lget C5aP) (EL 2 C5aE) (lget C5aR) (lget C5aL))
@[expose] noncomputable def c12643ky5a : ℕ → Bool := chunkK 60 (keyF (lget C5aP))
@[expose] noncomputable def c12643pt5c : ℕ → Bool :=
  chunkK 50 (pointK 315 9 2 50 GC5C (lget C5cP) (EL 2 C5cE) (lget C5cR) (lget C5cL))
@[expose] noncomputable def c12643ky5c : ℕ → Bool := chunkK 50 (keyF (lget C5cP))
@[expose] noncomputable def c12643pt7 : ℕ → Bool :=
  chunkK 7 (pointK 315 9 1 7 G7 (lget C7P) (EL 1 C7E) (lget C7R) (lget C7L))
@[expose] noncomputable def c12643ky7 : ℕ → Bool := chunkK 7 (keyF (lget C7P))
@[expose] noncomputable def c12643ptE : ℕ → Bool :=
  chunkK 60 (pointK 315 9 2 240 GCEP (lget CEP) (EL 2 CEE) (lget CER) (lget CEL))
@[expose] noncomputable def c12643kyE : ℕ → Bool := chunkK 60 (keyF (lget CEP))
@[expose] noncomputable def c12643ptD : ℕ → Bool :=
  chunkK 60 (pointK 315 9 2 60 GDP (lget DP) (EL 2 DE) (lget DR) (lget DL))
@[expose] noncomputable def c12643kyD : ℕ → Bool := chunkK 60 (keyF (lget DP))
@[expose] noncomputable def c12643ptS : ℕ → Bool :=
  chunkK 25 (pointK 315 9 2 25 GS5 (lget S5P) (EL 2 S5E) (lget S5R) (lget S5L))
@[expose] noncomputable def c12643kyS : ℕ → Bool := chunkK 25 (keyF (lget S5P))

end CertificateChecks.KernelC12643

end
