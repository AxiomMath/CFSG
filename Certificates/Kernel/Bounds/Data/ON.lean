module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.ON.Route
public import CFSG.Certificates.Kernel.Bounds.ON.T1vW0
public import CFSG.Certificates.Kernel.Bounds.ON.T1vW1
public import CFSG.Certificates.Kernel.Bounds.ON.T1vW2
public import CFSG.Certificates.Kernel.Bounds.ON.T1vC0
public import CFSG.Certificates.Kernel.Bounds.ON.T2vW0
public import CFSG.Certificates.Kernel.Bounds.ON.T2vC0
public import CFSG.Certificates.Kernel.Bounds.ON.T3vW0
public import CFSG.Certificates.Kernel.Bounds.ON.T3vC0

public section

#kb_cert CFSG.KBRoute.ON T1 ON_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/ON/data/ON_T1v.meta" 150458 8368350981384399335 CFSG.KBRoute.ON.rels
#kb_cert CFSG.KBRoute.ON T2 ON_T2v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/ON/data/ON_T2v.meta" 21395 5071441041055874478 CFSG.KBRoute.ON.rels
#kb_cert CFSG.KBRoute.ON T3 ON_T3v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/ON/data/ON_T3v.meta" 275 17620954660328610475 CFSG.KBRoute.ON.rels

namespace CFSG.KBRoute.ON

open CFSG.Certificates

@[expose] def facts : Prop :=
  T1.ok = true ∧ T2.ok = true ∧ T3.ok = true ∧ KB.topOk T1.amap 7 = true ∧
    KB.linkOk T2.amap T1.words = true ∧ KB.linkOk T3.amap T2.words = true

end CFSG.KBRoute.ON

end
