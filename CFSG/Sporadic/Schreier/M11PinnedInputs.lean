module

public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Monster.B.Mathieu.CertDataK
public import CFSG.Sporadic.Mathieu.M11
public meta import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Monster.B.Mathieu CFSG.Sporadic.Mathieu

@[expose] noncomputable def m11Record : GroupRecord := (MathieuCertificateK "M11").getD default

end CFSG.Sporadic.Schreier
