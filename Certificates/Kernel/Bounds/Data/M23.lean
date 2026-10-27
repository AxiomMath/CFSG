module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.M23.Route
public import CFSG.Certificates.Kernel.Bounds.M23.T1vW0
public import CFSG.Certificates.Kernel.Bounds.M23.T1vW1
public import CFSG.Certificates.Kernel.Bounds.M23.T1vC0
public import CFSG.Certificates.Kernel.Bounds.M23.T1vC1

public section

#kb_cert CFSG.KBRoute.M23 T1 M23_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/M23/data/M23_T1v.meta" 179167 12051786777623850778 CFSG.KBRoute.M23.rels

namespace CFSG.KBRoute.M23

open CFSG.Certificates

@[expose] def facts : Prop :=
  T1.ok = true ∧ KB.topOk T1.amap 2 = true ∧ KB.powOk T1.amap T1.words bottom rels = true

end CFSG.KBRoute.M23

end
