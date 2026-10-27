
module

public import CFSG.Sporadic.Schreier.ONCheckSmallAuxBase
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAuxBase

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.PSL3Four.Native

@[expose] def sqTabs : Array Tab := t32Enum.tabs.map fun t => comp 32 t t

@[expose] def sqEnum : Enum := enumBFS 32 sqTabs 200

@[expose] def omegaTabs : Array Tab := sqEnum.tabs.filter fun t => comp 32 t t == idTab 32

@[expose] def omegaEnum : Enum := enumBFS 32 omegaTabs 20

end CFSG.Sporadic.ONOddCore
