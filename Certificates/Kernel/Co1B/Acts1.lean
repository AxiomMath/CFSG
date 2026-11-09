module

public import Certificates.Kernel.Co1B.Acts0
public import Certificates.Data.Kernel.Misc.HexDrop
public meta import CFSG.Sporadic.Co1Block.PermData
public import CFSG.Certificates.Kernel.Misc.HexFlatGlue
import Certificates.Kernel.Misc.Perm.HexRowsCmd
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#kmisc_hexflat_rows CertificateChecks.KernelCo1B.AC1 CFSG.Sporadic.Co1Block.certActHex
  491400 5 840 20 117

public section

namespace CertificateChecks.KernelCo1B.AC1

open CFSG.KC.Misc.HexFlat

theorem p0 :
    runX 5 840 20 30 F (takeL 126000
      (dropL 491400 AC.chars)) 0 0 0 0 0 =
      true := by
  quickRfl

theorem p1 :
    runX 5 840 20 60 F (takeL 126000
      (dropL 126000 (dropL 491400 AC.chars))) 30 0 0 0 0 =
      true := by
  quickRfl

theorem p2 :
    runX 5 840 20 90 F (takeL 126000
      (dropL 126000 (dropL 126000 (dropL 491400 AC.chars)))) 60 0 0 0 0 =
      true := by
  quickRfl

theorem p3 :
    run 5 840 20 117 F
      (dropL 126000 (dropL 126000 (dropL 126000 (dropL 491400 AC.chars)))) 90 0 0 0 0 =
      true := by
  quickRfl

theorem all : hexFlat (dropL (nat_lit 491400) CertificateChecks.KernelCo1B.AC.chars) (nat_lit 5)
    (nat_lit 840) (nat_lit 20) (nat_lit 117) F = true := by
  have h : run 5 840 20 117 F (dropL 491400 AC.chars) 0 0 0 0 0 = true := by
    rw [← takeL_dropL 126000
      (dropL 491400 AC.chars),
      run_append (N := 117) (by decide) _ _ _ _ _ _ _ (by decide) p0]
    rw [← takeL_dropL 126000
      (dropL 126000 (dropL 491400 AC.chars)),
      run_append (N := 117) (by decide) _ _ _ _ _ _ _ (by decide) p1]
    rw [← takeL_dropL 126000
      (dropL 126000 (dropL 126000 (dropL 491400 AC.chars))),
      run_append (N := 117) (by decide) _ _ _ _ _ _ _ (by decide) p2]
    exact p3
  unfold hexFlat
  (rw [h]) <;> rfl

end CertificateChecks.KernelCo1B.AC1

end
