module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace Certificates.IvkL34

open CFSG.PSL3Four.Native

@[expose] def commB (n : Nat) (x y : Tab) : Bool := comp n x y == comp n y x

@[expose] def centCheck (r : Tab) (C ER : Array Tab) : Bool :=
  ER.all fun x => !commB 42 x r || !(C.all fun y => commB 42 x y) || x == idTab 42 || x == r

@[expose] def l34CentOK : Bool :=
  centCheck r₂T (centTabs 42 (enumBFS 42 gensS 20160).tabs r₂T) (enumBFS 42 gTabs 241920).tabs &&
    centCheck r₃T (centTabs 42 (enumBFS 42 gensS 20160).tabs r₃T) (enumBFS 42 gTabs 241920).tabs

end Certificates.IvkL34
