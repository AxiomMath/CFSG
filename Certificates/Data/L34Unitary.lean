module

public import Certificates.Data.L34Borel
public meta import Certificates.Data.L34Borel

public section

namespace Certificates.L34Unitary

open CFSG.PSL3Four.Native Certificates.L34Borel

@[expose] def t3bT : Tab :=
  #[0, 10, 12, 11, 9, 8, 5, 7, 6, 19, 20, 17, 18, 13, 15, 16, 14, 3, 2, 4, 1, 40, 22, 28, 32, 36,
    30, 23, 27, 37, 34, 24, 31, 29, 26, 25, 35, 33, 38, 21, 39, 41]

@[expose] def e0Gens : Array Tab := #[u0T, t3bT]

@[expose] def e0Enum : Enum := enumBFS 42 e0Gens 9

@[expose] def borelGens (j : Nat) : Array Tab := #[u0T] ++ sylGens[j]!

@[expose] def pairGens (r : Tab) (j : Nat) : Array Tab :=
  borelGens j ++ (borelGens j).map (conjTab 42 r r)

@[expose] def pairOK (r : Tab) (j : Nat) : Bool :=
  let E := enumBFS 42 (pairGens r j) 20160
  enumOK 42 (pairGens r j) E && E.tabs.size == 20160

@[expose] def l34UnitaryCheck (ES ER : Array Tab) : Bool :=
  found (indexOf ES) ES t3bT && enumOK 42 e0Gens e0Enum && e0Enum.tabs.size == 9 &&
    allBelow ER.size fun k =>
      let r := ER[k]!
      r == idTab 42 || !(comp 42 r r == idTab 42) || !(comp 42 r u0T == comp 42 u0T r) ||
        !(comp 42 r t3bT == comp 42 t3bT r) || allBelow 6 (pairOK r)

end Certificates.L34Unitary
