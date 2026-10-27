
module

public import CFSG.Monster.B.TwoA.Base.SevenPairCInputs
public import CFSG.Certificates.Kernel.SortTreeSound
public import Certificates.Kernel.MonsterB.Gl3064Data
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA CFSG.KC.SortTree CFSG.KLie.CT

namespace CertificateChecks.Batch3064

set_option maxRecDepth 100000

theorem t2 : treeOK actW2 2 (fun m => decide (m < 16)) (codeMat 2 1) (recT Gl3064.R2 6 12)
    6 4 2 3 64 1 = true := by quickRfl

theorem e2 : closeOK actW2 2 (recT Gl3064.R2 6 12) (fun i k => fget (recT Gl3064.E2 6 8 i) k 3)
    6 4 64 1 = true := by quickRfl

theorem t3 : treeOK actW3 5 (fun m => decide (m < 512)) (codeMat 3 1) (recT Gl3064.R3 6 24)
    168 9 3 8 64 3 = true := by quickRfl

theorem e3 : closeOK actW3 5 (recT Gl3064.R3 6 24) (fun i k => fget (recT Gl3064.E3 6 40 i) k 8)
    168 9 64 3 = true := by quickRfl

theorem c2 : natCertOK actW2 2 (fun m => decide (m < 16)) (codeMat 2 1) glCert2 = true ∧
    glCert2.pts.size = 6 := by
  obtain ⟨h1, h2, -⟩ := natBfs_tree (fuel := 100) (by norm_num) (by norm_num) t2 e2
  exact ⟨h1, h2⟩

theorem c3 : natCertOK actW3 5 (fun m => decide (m < 512)) (codeMat 3 1) glCert3 = true ∧
    glCert3.pts.size = 168 := by
  obtain ⟨h1, h2, -⟩ := natBfs_tree (fuel := 1000) (by norm_num) (by norm_num) t3 e3
  exact ⟨h1, h2⟩

end CertificateChecks.Batch3064

namespace Certificates

open CertificateChecks

end Certificates
