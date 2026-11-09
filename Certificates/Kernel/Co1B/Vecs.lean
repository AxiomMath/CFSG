module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Misc.HexFlatGlue
import Certificates.Kernel.Misc.Perm.HexCmd
import Certificates.Kernel.Misc.Perm.HexRowsCmd
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCo1B.CV CFSG.Sporadic.Co1Block.certVecHex
#kmisc_hexflat_rows CertificateChecks.KernelCo1B.CV CFSG.Sporadic.Co1Block.certVecHex 0 6 840 24 117

public section

namespace CertificateChecks.KernelCo1B.CV

open CFSG.KC.Misc.HexFlat

theorem p0 :
    runX 6 840 24 30 F (takeL 151200
      chars) 0 0 0 0 0 =
      true := by
  quickRfl

theorem p1 :
    runX 6 840 24 60 F (takeL 151200
      (dropL 151200 chars)) 30 0 0 0 0 =
      true := by
  quickRfl

theorem p2 :
    runX 6 840 24 90 F (takeL 151200
      (dropL 151200 (dropL 151200 chars))) 60 0 0 0 0 =
      true := by
  quickRfl

theorem p3 :
    run 6 840 24 117 F
      (dropL 151200 (dropL 151200 (dropL 151200 chars))) 90 0 0 0 0 =
      true := by
  quickRfl

theorem all : hexFlat chars (nat_lit 6) (nat_lit 840) (nat_lit 24) (nat_lit 117) F = true := by
  have h : run 6 840 24 117 F chars 0 0 0 0 0 = true := by
    rw [← takeL_dropL 151200
      chars,
      run_append (N := 117) (by decide) _ _ _ _ _ _ _ (by decide) p0]
    rw [← takeL_dropL 151200
      (dropL 151200 chars),
      run_append (N := 117) (by decide) _ _ _ _ _ _ _ (by decide) p1]
    rw [← takeL_dropL 151200
      (dropL 151200 (dropL 151200 chars)),
      run_append (N := 117) (by decide) _ _ _ _ _ _ _ (by decide) p2]
    exact p3
  unfold hexFlat
  (rw [h]) <;> rfl

end CertificateChecks.KernelCo1B.CV

end
