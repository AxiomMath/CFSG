module

public import Certificates.Data.CFSGNative.AS91.M24Kzero
public import Certificates.Data.Kernel.M24G.FixOct
public import Certificates.Data.Kernel.M24G.Replay

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G CFSG.KC.ONanSmall

@[expose] def kzeroKeyF (t : Array Nat) : Nat :=
  if t.size = 24 then t.toList.foldl (fun acc x => (acc <<< 5) ||| x) 0 else Native.kzeroKey t

@[expose] def kzeroStepsF : List (Array Nat → Array Nat) := Native.s0Tabs.map mulTabF

@[expose] def kzeroConjF (p : Array Nat × Array Nat) (x : Array Nat) : Array Nat :=
  mulTabF p.1 (mulTabF x p.2)

@[expose] def kzeroK0F (pos : KTree (Nat × Nat)) (L : List (Array Nat))
    (p : Array Nat × Array Nat) : List (Array Nat) :=
  L.filter fun t => (findK (kzeroKeyF (kzeroConjF p t)) pos).isSome

@[expose] def kzeroPairF : Array Nat × Array Nat :=
  (Native.kzeroUInv.headD #[], Native.uTabs.headD #[])

end CFSG.KC.M24G
