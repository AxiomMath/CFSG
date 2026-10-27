module

public import Certificates.Data.Kernel.BstBfs
public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.Check

public section

namespace CFSG.KC.GapsK

open CFSG.KC.BstBfs CFSG.KC.S97RYK CFSG.KC.Enum CFSG.KC.LQT.PW CFSG.CGT.Timmesfeld75.WCCheck
open CFSG.Sporadic.Th.Native CFSG.RankThree.GF2n.Tim81.Gaps

@[expose] noncomputable def conjK (n cP ciP x : Nat) : Nat := mulK n (mulK n cP x) ciP

@[expose] noncomputable def basisK (n : Nat) (us : List Nat) : List Nat → List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat → List Nat) (fun _ acc => acc)
    (fun u _ ih sp acc => bIfK (memK sp u) (ih sp acc)
      (forceL (sp ++ sp.map fun x => mulK n x u) fun sp' => ih sp' (u :: acc))) us

@[expose] noncomputable def closK (n fuel idP : Nat) (us vs S : List Nat) (k : List Nat → Bool) :
    Bool :=
  insC BT.lf idP fun t0 =>
  bfsB (mulK n) S fuel t0 [idP] fun t =>
  forceL (inorder t []) fun E =>
  bAnd(memB t idP, bAnd(sincL E, bAnd(S.all (memK (us ++ vs)),
    bAnd((us ++ vs).all (memB t), bAnd(E.all fun x => S.all fun s => memB t (mulK n x s), k E)))))

@[expose] noncomputable def closJ (D : Data) (fuel idP : Nat) (pcP : List Nat) (J : List Bool)
    (c : List Int) (k : List Nat → List Nat → Bool) : Bool :=
  strictK (wK D c) fun cP => strictK (wK D (invWord c)) fun ciP =>
  forceL (idP :: (idxU D J).map (eltK D.n idP pcP)) fun us =>
  forceL (us.map (conjK D.n cP ciP)) fun vs =>
  forceL (basisK D.n us [idP] []) fun B =>
  forceL (B ++ B.map (conjK D.n cP ciP)) fun S =>
  closK D.n fuel idP us vs S (k S)

@[expose] noncomputable def bmK (B : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun i _ ih => Nat.lor (Nat.shiftLeft 1 i) ih) B

@[expose] noncomputable def imgMK (x : Nat) (B : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun i _ ih => Nat.lor (Nat.shiftLeft 1 (imgW 5 x i)) ih) B

@[expose] noncomputable def fixK (bs : List (List Nat)) (x : Nat) : Bool :=
  bs.all fun B => Nat.beq (imgMK x B) (bmK B)

@[expose] noncomputable def cntK (bs : List (List Nat)) (E : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => bIfK (fixK bs x) (Nat.succ ih) ih) E

@[expose] noncomputable def blocksK (n : Nat) (bs : List (List Nat)) (S : List Nat) : Bool :=
  decide (bs.length = 5) && decide bs.Nodup &&
    bs.all (fun B => !B.isEmpty && decide B.Nodup && B.all (· < n)) &&
    (List.range 5).all (fun i => (List.range 5).all fun j =>
      i == j || (bs.getD i []).all fun x => !(bs.getD j []).contains x) &&
    S.all fun s => bs.all fun B => memK (bs.map bmK) (imgMK s B)

@[expose] noncomputable def gverdictK (D : Data) (fuel idP : Nat) (pcP : List Nat)
    (J : List Bool) (v : GVerdict) : Bool :=
  GVerdict.rec (motive := fun _ => Bool)
    (Nat.blt ((idxU D J).length + 1) 4)
    (fun i j => (idxU D J).contains i && (idxU D J).contains j &&
      !memUK D idP pcP J (mulK D.n (eltK D.n idP pcP i) (eltK D.n idP pcP j)))
    (fun t y g =>
      strictK (wK D g) fun gP => strictK (wK D (invWord g)) fun giP =>
      (idxU D J).contains t && (idxU D J).contains y &&
      !Nat.beq (eltK D.n idP pcP t) idP &&
      ((idP :: (idxU D J).map (eltK D.n idP pcP)).all fun u =>
        commK D.n (conjK D.n gP giP u) (eltK D.n idP pcP t)) &&
      !memUK D idP pcP J (conjK D.n gP giP (eltK D.n idP pcP y)))
    (fun c a b => closJ D fuel idP pcP J c fun _ E =>
      bAnd(Nat.beq E.length (2 ^ a * 3 ^ b), Nat.blt 0 b))
    (fun c bs a => closJ D fuel idP pcP J c fun S E =>
      bAnd(Nat.beq E.length (2 ^ a * 60), bAnd(blocksK D.n bs S, Nat.beq (cntK bs E) (2 ^ a))))
    v

@[expose] noncomputable def gapsVerdictsK (P : GData) : Bool :=
  Nat.blt P.D.n 32 && Nat.blt 0 P.D.n &&
  strictK (encK P.D.n (idT P.D.n)) fun idP =>
  forceL (P.D.pc.map (wK P.D)) fun pcP =>
  (allMasks P.D.cls.length).all fun J =>
    P.gv.any fun p => p.1 == J && gverdictK P.D P.fuel idP pcP J p.2

@[expose] noncomputable def gapsBaseK (D : Data) : Bool :=
  let n := D.n
  Nat.blt n 32 &&
  strictK (encK n (idT n)) fun idP =>
  forceL (D.pc.map (wK D)) fun pcP =>
  forceL (D.pc.map fun w => wK D (invWord w)) fun pciP =>
  forceL ((List.range (2 ^ D.pc.length)).map (eltK n idP pcP)) fun SP =>
  forceL (SP.map (invW n 5)) fun SiP =>
  forceL (D.cw.map (wK D)) fun cwP =>
  forceL (D.cw.map fun w => wK D (invWord w)) fun cwiP =>
  forceL ((D.cls.flatMap fun c => c.map Prod.fst).map (eltK n idP pcP)) fun clP =>
  strictK (eltK n idP pcP D.zIdx) fun zP =>
  baseK D idP pcP pciP SP SiP cwP cwiP clP zP

end CFSG.KC.GapsK

end
