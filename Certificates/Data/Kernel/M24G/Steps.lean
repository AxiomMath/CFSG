module

public import Certificates.Data.Kernel.M24G.Img
public import Certificates.Data.Kernel.M24G.Lists
public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

@[expose] def imgTrioF (t : List Nat) (x : Nat × Nat × Nat) : Nat × Nat × Nat :=
  Native.sort3 (imgF (imgTab t) x.1) (imgF (imgTab t) x.2.1) (imgF (imgTab t) x.2.2)

@[expose] def imgSextF (t : List Nat) (s : List Nat) : List Nat :=
  sortN (s.map (imgF (imgTab t)))

@[expose] def trioStepsF : List (Nat × Nat × Nat → Nat × Nat × Nat) :=
  Native.genTabs.map fun t => imgTrioF t.toList

@[expose] def sextStepsF : List (List Nat → List Nat) :=
  Native.genTabs.map fun t => imgSextF t.toList

end CFSG.KC.M24G
