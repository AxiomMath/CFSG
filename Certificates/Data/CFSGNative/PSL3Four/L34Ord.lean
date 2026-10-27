module

public import Certificates.Data.CFSGNative.PSL3Four.L34Aut

public section

namespace CFSG.PSL3Four.Native

@[expose] def l34OrdCheck (ES : Array Tab) : Bool :=
  allBelow ES.size fun k =>
    (!(powTab 42 ES[k]! 15 == idTab 42) || powTab 42 ES[k]! 3 == idTab 42 ||
        powTab 42 ES[k]! 5 == idTab 42) &&
      (!(powTab 42 ES[k]! 21 == idTab 42) || powTab 42 ES[k]! 3 == idTab 42 ||
        powTab 42 ES[k]! 7 == idTab 42)

end CFSG.PSL3Four.Native
