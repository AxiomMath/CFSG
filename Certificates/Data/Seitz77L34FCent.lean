module

public import Certificates.Data.CFSGNative.PSL3Four.L34Syl
public meta import Certificates.Data.CFSGNative.PSL3Four.L34Syl

public section

namespace Certificates.Seitz77L34

open CFSG.PSL3Four.Native

@[expose] def l34FCentCheck (ER : Array Tab) : Bool :=
  let EF := enumBFS 42 fGens 16
  let idxF := indexOf EF.tabs
  enumOK 42 fGens EF && EF.tabs.size == 16 && centScanOK 42 ER EF.tabs EF.tabs &&
    anyBelow EF.tabs.size fun a => !found idxF EF.tabs (conjTab 42 r₃T r₃T EF.tabs[a]!)

end Certificates.Seitz77L34
