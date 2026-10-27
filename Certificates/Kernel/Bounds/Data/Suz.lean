module

public import Certificates.Data.Kernel.Bounds.Table
public import Certificates.Kernel.Bounds.Suz.Route
public import Certificates.Kernel.Bounds.Suz.T1vW0
public import Certificates.Kernel.Bounds.Suz.T1vC0
public import Certificates.Kernel.Bounds.Suz.T2vW0
public import Certificates.Kernel.Bounds.Suz.T2vC0
public import Certificates.Kernel.Bounds.Suz.T3vW0
public import Certificates.Kernel.Bounds.Suz.T3vC0
public import Certificates.Kernel.Bounds.Suz.T4vW0
public import Certificates.Kernel.Bounds.Suz.T4vC0

public section

#kb_cert CFSG.KBRoute.Suz T1 Suz_T1v include_bytes "../Suz/data/Suz_T1v.meta" 3149 9308309354496609925 CFSG.KBRoute.Suz.rels
#kb_cert CFSG.KBRoute.Suz T2 Suz_T2v include_bytes "../Suz/data/Suz_T2v.meta" 729 17567991394435746506 CFSG.KBRoute.Suz.rels
#kb_cert CFSG.KBRoute.Suz T3 Suz_T3v include_bytes "../Suz/data/Suz_T3v.meta" 431 2536992008051246648 CFSG.KBRoute.Suz.rels
#kb_cert CFSG.KBRoute.Suz T4 Suz_T4v include_bytes "../Suz/data/Suz_T4v.meta" 5057 4390005806162259891 CFSG.KBRoute.Suz.rels

namespace CFSG.KBRoute.Suz

open CFSG.Certificates

@[expose] def facts : Prop :=
  T1.ok = true ∧ T2.ok = true ∧ T3.ok = true ∧ T4.ok = true ∧ KB.topOk T1.amap 7 = true ∧
    KB.topOk T2.amap 6 = true ∧ KB.topOk T3.amap 5 = true ∧ KB.topOk T4.amap 4 = true ∧
    KB.linkOk T2.amap T1.words = true ∧ KB.linkOk T3.amap T2.words = true ∧
    KB.linkOk T4.amap T3.words = true

end CFSG.KBRoute.Suz

end
