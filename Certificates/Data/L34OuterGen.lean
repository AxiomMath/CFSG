module

public import Certificates.Data.CFSGNative.PSL3Four.L34Aut
public meta import Certificates.Data.CFSGNative.PSL3Four.L34Aut

public section

namespace Certificates.L34OuterGen

open CFSG.PSL3Four.Native

@[expose] def t3aT : Tab :=
  #[13, 1, 5, 17, 9, 15, 14, 0, 16, 19, 10, 3, 8, 7, 18, 2, 12, 11, 6, 4, 20, 29, 38, 23, 32, 35,
    21, 27, 28, 26, 40, 24, 31, 34, 39, 36, 25, 30, 41, 33, 37, 22]

@[expose] def t3bT : Tab :=
  #[0, 10, 12, 11, 9, 8, 5, 7, 6, 19, 20, 17, 18, 13, 15, 16, 14, 3, 2, 4, 1, 40, 22, 28, 32, 36,
    30, 23, 27, 37, 34, 24, 31, 29, 26, 25, 35, 33, 38, 21, 39, 41]

@[expose] def t3Gens : Array Tab := #[t3aT, t3bT]

@[expose] def t3Enum : Enum := enumBFS 42 t3Gens 9

@[expose] def normsOK (ET : Array Tab) (x : Tab) : Bool :=
  allBelow ET.size fun j => anyBelow ET.size fun j' => comp 42 x ET[j]! == comp 42 ET[j']! x

@[expose] def outerGenScan (ET : Enum) (ES ER : Array Tab) : Bool :=
  let idxT := indexOf ET.tabs
  allBelow ER.size fun k =>
    !(powTab 42 ER[k]! 3 == idTab 42) || !normsOK ET.tabs ER[k]! || found idxT ET.tabs ER[k]! ||
      anyBelow ES.size fun s =>
        comp 42 ER[k]! ES[s]! == comp 42 ES[s]! ER[k]! && !normsOK ET.tabs ES[s]!

@[expose] def l34OuterGenCheck (ES ER : Array Tab) : Bool :=
  (allBelow t3Gens.size fun j => memTab ES t3Gens[j]!) && enumOK 42 t3Gens t3Enum &&
    t3Enum.tabs.size == 9 && outerGenScan t3Enum ES ER

end Certificates.L34OuterGen
