module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.KuAct

open CFSG.PSL3Four.Native

@[expose] def pow32Tab (t : Tab) : Tab :=
  let t₂ := comp 42 t t
  let t₄ := comp 42 t₂ t₂
  let t₈ := comp 42 t₄ t₄
  let t₁₆ := comp 42 t₈ t₈
  comp 42 t₁₆ t₁₆

@[expose] def centR₄ : Array Tab := centTabs 42 (enumBFS 42 gTabs 241920).tabs r₄T

@[expose] def sqC₄ : Array Tab :=
  (centTabs 42 (enumBFS 42 gensS 20160).tabs r₄T).map fun s => comp 42 s s

@[expose] def kuActOK : Bool :=
  centR₄.all fun ρ => !(sqC₄.all fun q => comp 42 ρ q == comp 42 q ρ) || pow32Tab ρ == idTab 42

end CFSG.ComponentClassification.GrSLit.L34Facts.KuAct
