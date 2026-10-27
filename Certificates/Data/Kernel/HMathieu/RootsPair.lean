module

public import Certificates.Data.Kernel.HMathieu.Roots
public import CFSG.Quasithin.H13.A5M12SylInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM11
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Bridge.M23Surj

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

@[expose] noncomputable def dodK (g : Nat) : Bool :=
  permM (unpk g) dodecadMask == dodecadMask ||
    permM (unpk g) dodecadMask == dodecadMask ^^^ (2 ^ 24 - 1)

@[expose] noncomputable def rootPairK (np : Nat) (gs E : List Nat) : Bool :=
  rootK 0 np gs E && gs.all dodK

end CFSG.KC.HMathieu

end
