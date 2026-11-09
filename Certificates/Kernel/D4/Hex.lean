module

public import Certificates.Data.Item434D42
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatRows
import Certificates.Kernel.Misc.Perm.HexTabCmd
import CFSG.Certificates.Kernel.Common.Harness
meta import Certificates.Data.Item434D42

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelD4.HX CFSG.RankThree.PartTwo.Sec4.Item434D42.d4Hex
#kmisc_hexflat_tab CertificateChecks.KernelD4.HX CFSG.RankThree.PartTwo.Sec4.Item434D42.d4Hex 3 2457 12 91

public section

namespace CertificateChecks.KernelD4.HX

open CFSG.KC.Misc.HexFlat

theorem p0 :
    CFSG.KC.Misc.HexFlat.run 3 2457 12 13 F (dropL 0 (dropL 0 chars)) 0 0 0 0 0 =
      true := by quickRfl
theorem p1 :
    CFSG.KC.Misc.HexFlat.run 3 2457 12 26 F (dropL 95823 (dropL 0 chars)) 13 0 0 0 0 =
      true := by quickRfl
theorem p2 :
    CFSG.KC.Misc.HexFlat.run 3 2457 12 39 F (dropL 191646 (dropL 0 chars)) 26 0 0 0 0 =
      true := by quickRfl
theorem p3 :
    CFSG.KC.Misc.HexFlat.run 3 2457 12 52 F (dropL 287469 (dropL 0 chars)) 39 0 0 0 0 =
      true := by quickRfl
theorem p4 :
    CFSG.KC.Misc.HexFlat.run 3 2457 12 65 F (dropL 383292 (dropL 0 chars)) 52 0 0 0 0 =
      true := by quickRfl
theorem p5 :
    CFSG.KC.Misc.HexFlat.run 3 2457 12 78 F (dropL 79116 (dropL 399999 chars)) 65 0 0 0 0 =
      true := by quickRfl
theorem p6 :
    CFSG.KC.Misc.HexFlat.run 3 2457 12 91 F (dropL 174939 (dropL 399999 chars)) 78 0 0 0 0 =
      true := by quickRfl

theorem rows : RowsD chars 3 2457 12 F 0 91 :=
  rowsD_cat (rowsD_of_run (by decide) (by decide) (by decide) (by decide) p0) <|
  rowsD_cat (rowsD_of_run (by decide) (by decide) (by decide) (by decide) p1) <|
  rowsD_cat (rowsD_of_run (by decide) (by decide) (by decide) (by decide) p2) <|
  rowsD_cat (rowsD_of_run (by decide) (by decide) (by decide) (by decide) p3) <|
  rowsD_cat (rowsD_of_run (by decide) (by decide) (by decide) (by decide) p4) <|
  rowsD_cat (rowsD_of_run (by decide) (by decide) (by decide) (by decide) p5) <|
  (rowsD_of_run (by decide) (by decide) (by decide) (by decide) p6)

end CertificateChecks.KernelD4.HX

end
