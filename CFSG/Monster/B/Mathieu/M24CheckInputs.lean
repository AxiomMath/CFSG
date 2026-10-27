module

public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Monster.B.Mathieu.CertDataK
public import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Sporadic.Mathieu

@[expose] noncomputable def m24Record : GroupRecord := (MathieuCertificateK "M24").getD default

end CFSG.Monster.B.Mathieu
