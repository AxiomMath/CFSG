module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.ComponentClassification.SolMax.L34Graph

open CFSG.PSL3Four.Native

@[expose] def l34GraphUnitaryCheck : Bool :=
  let ES := enumBFS 42 gensS 20160
  let O₄ := orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₄T 1963
  let C₃ := centTabs 42 ES.tabs r₃T
  O₄.tabs.toList.all fun u =>
    !(comp 42 u r₃T == comp 42 r₃T u) ||
      C₃.toList.all fun s => C₃.toList.any fun x =>
        !(comp 42 (comp 42 (comp 42 u x) u) s == comp 42 s x)

end CFSG.ComponentClassification.SolMax.L34Graph
