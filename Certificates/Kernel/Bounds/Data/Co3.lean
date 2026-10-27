module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.Co3Alt.Route
public import CFSG.Certificates.Kernel.Bounds.Co3.T1vW0
public import CFSG.Certificates.Kernel.Bounds.Co3.T1vW1
public import CFSG.Certificates.Kernel.Bounds.Co3.T1vW2
public import CFSG.Certificates.Kernel.Bounds.Co3.T1vW3
public import CFSG.Certificates.Kernel.Bounds.Co3.T1vW4
public import CFSG.Certificates.Kernel.Bounds.Co3.T1vW5
public import CFSG.Certificates.Kernel.Bounds.Co3.T1vW6
public import CFSG.Certificates.Kernel.Bounds.Co3.T1vC0
public import CFSG.Certificates.Kernel.Bounds.Co3Alt.T2vW0
public import CFSG.Certificates.Kernel.Bounds.Co3Alt.T2vC0
public import CFSG.Certificates.Kernel.Bounds.Co3Alt.T3vW0
public import CFSG.Certificates.Kernel.Bounds.Co3Alt.T3vC0

public section

#kb_cert CFSG.KBRoute.Co3Alt T1 Co3_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/Co3/data/Co3_T1v.meta" 444782 11767286554750447795 CFSG.KBRoute.Co3Alt.rels
#kb_cert CFSG.KBRoute.Co3Alt T2 Co3Alt_T2v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/Co3Alt/data/Co3Alt_T2v.meta" 8300 12552019413653892842 CFSG.KBRoute.Co3Alt.rels
#kb_cert CFSG.KBRoute.Co3Alt T3 Co3Alt_T3v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/Co3Alt/data/Co3Alt_T3v.meta" 508 12915761034985254573 CFSG.KBRoute.Co3Alt.rels

namespace CFSG.KBRoute.Co3Alt

open CFSG.Certificates

@[expose] def facts : Prop :=
  T1.ok = true ∧ T2.ok = true ∧ T3.ok = true ∧ KB.topOk T1.amap 7 = true ∧
    KB.linkOk T2.amap T1.words = true ∧ KB.linkOk T3.amap T2.words = true

end CFSG.KBRoute.Co3Alt

end
