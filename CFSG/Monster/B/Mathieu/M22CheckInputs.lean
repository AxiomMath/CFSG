module

public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Monster.B.Mathieu.CertDataK
public import CFSG.Sporadic.Mathieu.M22
public meta import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Sporadic.Mathieu

@[expose] noncomputable def m22Record : GroupRecord := (MathieuCertificateK "M22").getD default

end CFSG.Monster.B.Mathieu
