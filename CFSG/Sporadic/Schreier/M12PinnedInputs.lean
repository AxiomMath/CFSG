module

public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Monster.B.Mathieu.CertDataK
public import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Monster.B.Mathieu CFSG.Sporadic.Mathieu

@[expose] noncomputable def m12Record : GroupRecord := (MathieuCertificateK "M12").getD default

end CFSG.Sporadic.Schreier
