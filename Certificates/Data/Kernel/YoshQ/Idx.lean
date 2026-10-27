module

public import Certificates.Data.Kernel.YoshQ.Replay
public import Certificates.Data.Kernel.YoshQ.Twin

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def bucketN (n w : Nat) (R : List (List (List Nat))) (x : Nat) : List Nat :=
  (R.getD (apN n w x 0) []).getD (apN n w x 1) []

@[expose] noncomputable def idxN (n w : Nat) (R : List (List (List Nat))) (x : Nat) : Nat :=
  match (bucketN n w R x).find? (fun e => Nat.beq (e >>> 12) (x % 2 ^ (n * w))) with
  | some e => e % 4096
  | none => 4096

@[expose] noncomputable def idxOK (n w cnt EP : Nat) (R : List (List (List Nat))) : Bool :=
  R.all (fun r => r.all (fun b => b.all fun e =>
    Nat.blt (e % 4096) cnt && Nat.beq (fldN EP (n * w) (e % 4096)) (e >>> 12))) &&
  allN cnt (fun i => (bucketN n w R (fldN EP (n * w) i)).any
    (fun e => Nat.beq e (fldN EP (n * w) i * 4096 + i)))

@[expose] noncomputable def maskN (n w : Nat) (R : List (List (List Nat))) (L : List Nat) : Nat :=
  L.foldl (fun M x => M ||| (1 <<< idxN n w R x)) 0

@[expose] noncomputable def memI (n w cnt : Nat) (R : List (List (List Nat))) (L : List Nat)
    (x : Nat) : Bool :=
  Nat.blt (idxN n w R x) cnt && (maskN n w R L).testBit (idxN n w R x)

@[expose] noncomputable def allIn (n w cnt : Nat) (R : List (List (List Nat))) (L : List Nat) :
    Bool :=
  L.all fun x => Nat.blt (idxN n w R x) cnt

open CFSG.EvenSporadicStandard.M12Std.Yosh

@[expose] noncomputable def fusionCoverI (cnt : Nat) (R : List (List (List Nat))) (GS NL : List Nat)
    (α k : Nat) : Bool :=
  allIn 16 5 cnt R (goodTabsN GS NL α k) && allIn 16 5 cnt R (badTabsN GS NL α k) &&
  (NL.all (fun y => !involN 16 5 y || memI 16 5 cnt R (goodTabsN GS NL α k) y ||
      memI 16 5 cnt R (badTabsN GS NL α k) y) &&
    (NL.filter (memI 16 5 cnt R (goodTabsN GS NL α k))).length == goodCount α)

end CFSG.KC.YoshQ

end
