module

public import Certificates.Kernel.AxisPlane.Baby.R0
public import Certificates.Kernel.AxisPlane.Baby.R4
public import Certificates.Kernel.AxisPlane.Baby.R7
public import Certificates.Kernel.AxisPlane.Baby.W0
public import Certificates.Kernel.AxisPlane.Baby.W5
public import Certificates.Kernel.AxisPlane.Baby.Stmt

public section

namespace CertificateChecks.KernelAP.Baby

open CFSG.Monster.AxisCount.Baby

theorem cover0 : BabyStmt babyOrbit0 :=
  stmt_of words0 R0.chk rfl (by decide +kernel) (by decide +kernel)
theorem cover1 : BabyStmt babyOrbit1 :=
  stmt_of words1 R1.chk rfl (by decide +kernel) (by decide +kernel)
theorem cover2 : BabyStmt babyOrbit2 :=
  stmt_of words2 R2.chk rfl (by decide +kernel) (by decide +kernel)
theorem cover3 : BabyStmt babyOrbit3 :=
  stmt_of words3 R3.chk rfl (by decide +kernel) (by decide +kernel)
theorem cover4 : BabyStmt babyOrbit4 :=
  stmt_of words4 R4.chk rfl (by decide +kernel) (by decide +kernel)
theorem cover5 : BabyStmt babyOrbit5 :=
  stmt_of words5 R5.chk rfl (by decide +kernel) (by decide +kernel)
theorem cover6 : BabyStmt babyOrbit6 :=
  stmt_of words6 R6.chk rfl (by decide +kernel) (by decide +kernel)
theorem cover7 : BabyStmt babyOrbit7 :=
  stmt_of words7 R7.chk rfl (by decide +kernel) (by decide +kernel)
theorem cover8 : BabyStmt babyOrbit8 :=
  stmt_of words8 R8.chk rfl (by decide +kernel) (by decide +kernel)
theorem cover9 : BabyStmt babyOrbit9 :=
  stmt_of words9 R9.chk rfl (by decide +kernel) (by decide +kernel)

end CertificateChecks.KernelAP.Baby

end
