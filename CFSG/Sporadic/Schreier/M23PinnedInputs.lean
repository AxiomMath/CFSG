module

public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Monster.B.Mathieu.CertDataK
public import CFSG.Sporadic.Schreier.M23Gens
public meta import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Schreier.M23Gens

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Monster.B.Mathieu

@[expose] noncomputable def m23Record : GroupRecord := (MathieuCertificateK "M23").getD default

end CFSG.Sporadic.Schreier
