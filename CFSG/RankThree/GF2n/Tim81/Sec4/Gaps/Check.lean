module

public import CFSG.LargeExtraspecial.S97RYCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc

public section

namespace CFSG.RankThree.GF2n.Tim81.Gaps

open CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75.WCCheck
open CFSG.LargeExtraspecial.S11.PairCheck
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

inductive GVerdict where
  | small
  | notClosed (i j : Nat)
  | bad (t y : Nat) (g : List Int)
  | solv (c : List Int) (a b : Nat)
  | alt5 (c : List Int) (blocks : List (List Nat)) (a : Nat)

structure GData where
  D : Data
  fuel : Nat
  gv : List (List Bool × GVerdict)

@[expose] def rnOfTable (n : Nat) [NeZero n] (t : Table) : RN n :=
  ⟨Vector.ofFn fun i => Fin.ofNat n ((t[i.val]!).toNat)⟩

@[expose] def closureGens (D : Data) [NeZero D.n] (J : List Bool) (c : List Int) :
    List (RN D.n) :=
  (tabU D J ++ tabUc D J c).map (rnOfTable D.n)

@[expose] def closureSet (D : Data) [NeZero D.n] (fuel : Nat) (J : List Bool) (c : List Int) :
    Std.HashSet (RN D.n) :=
  bfsSet (closureGens D J c) fuel

@[expose] def closureOK (D : Data) [NeZero D.n] (fuel : Nat) (J : List Bool)
    (c : List Int) : Bool :=
  closedH (closureGens D J c) (closureSet D fuel J c)

@[expose] def closureSize (D : Data) [NeZero D.n] (fuel : Nat) (J : List Bool)
    (c : List Int) : Nat :=
  (closureSet D fuel J c).size

@[expose] def blockImg (t : Table) (B : List Nat) : List Nat :=
  (B.map fun i => (t.getD i 0).toNat).mergeSort fun a b => decide (a ≤ b)

@[expose] def blockFinset (n : Nat) [NeZero n] (B : List Nat) : Finset (Fin n) :=
  B.toFinset.image fun x => Fin.ofNat n x

@[expose] def blockIndex (bs : List (List Nat)) (B : List Nat) : Nat :=
  bs.idxOf B

@[expose] def blockImgRN (n : Nat) [NeZero n] (x : RN n) (B : List Nat) : List Nat :=
  (B.map fun i => (x.val[(Fin.ofNat n i)]).val).mergeSort fun a b => decide (a ≤ b)

@[expose] def blocksFixed (n : Nat) [NeZero n] (x : RN n) (bs : List (List Nat)) : Bool :=
  bs.all fun B => decide (blockFinset n (blockImgRN n x B) = blockFinset n B)

@[expose] def fixedCount (D : Data) [NeZero D.n] (fuel : Nat) (J : List Bool) (c : List Int)
    (bs : List (List Nat)) : Nat :=
  ((closureSet D fuel J c).toList.filter (fun x => blocksFixed D.n x bs)).length

@[expose] def blocksOK (D : Data) (J : List Bool) (c : List Int) (bs : List (List Nat)) : Bool :=
  decide (bs.length = 5) && decide bs.Nodup &&
    bs.all (fun B => !B.isEmpty && decide B.Nodup && B.all (· < D.n)) &&
    (List.range 5).all (fun i => (List.range 5).all fun j =>
      i == j || (bs.getD i []).all fun x => !(bs.getD j []).contains x) &&
    (tabU D J ++ tabUc D J c).all fun t =>
      (List.range 5).all fun i =>
        blockIndex bs (blockImg t (bs.getD i [])) < 5

@[expose] def gverdictOK (P : GData) (J : List Bool) : GVerdict → Bool
  | .small => (idxU P.D J).length + 1 < 4
  | .notClosed i j => verdictOK P.D J (.notClosed i j)
  | .bad t y g => (idxU P.D J).contains t && (idxU P.D J).contains y &&
      !(el P.D t == idT P.D.n) &&
      ((tabU P.D J).all fun u => commT P.D.n (conjW P.D g u) (el P.D t)) &&
      !memU P.D J (conjW P.D g (el P.D y))
  | .solv c a b =>
      if hn : 0 < P.D.n then
        letI : NeZero P.D.n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
        closureOK P.D P.fuel J c && closureSize P.D P.fuel J c == 2 ^ a * 3 ^ b &&
          decide (1 ≤ b)
      else false
  | .alt5 c blocks a =>
      if hn : 0 < P.D.n then
        letI : NeZero P.D.n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
        closureOK P.D P.fuel J c && closureSize P.D P.fuel J c == 2 ^ a * 60 &&
          blocksOK P.D J c blocks && fixedCount P.D P.fuel J c blocks == 2 ^ a
      else false

end CFSG.RankThree.GF2n.Tim81.Gaps
