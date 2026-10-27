module

public import Certificates.Data.MaxD2Heis

public section

namespace Certificates.MaxD2Heis

open CFSG.PSL3Four.Native
open Certificates.MaxD2Perm

@[expose] def zElt (D : Data) : Tab := (zTabs D)[1]!

@[expose] def zOrbit (D : Data) : Enum :=
  orbitBFS D.n D.gT (giT D) (zElt D) ((D.p - 1) * D.gOrder / D.nOrder + 1)

@[expose] def checkHClass (D : Data) : Bool :=
  let z := zElt D
  let E := zOrbit D
  !(z == idTab D.n) && orbitOK D.n D.gT (giT D) z E &&
    decide ((D.p - 1) * D.gOrder ≤ D.nOrder * E.tabs.size)

@[expose] def checkHeisEq (D : Data) : Bool :=
  checkInv D && checkHR D && checkN D && checkHNormal D && checkHZ D && checkHExp D &&
    checkHComm D && checkHTorus D && checkHCent D && checkHClass D

end Certificates.MaxD2Heis
