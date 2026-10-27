module

public import Certificates.Data.GMS78RuCzEnum
public import Certificates.Data.GMS78RuCzRigidData
public import Certificates.Data.GMS78RuCzJCert
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutETableDefs

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open CFSG.CosetTable CFSG.Sporadic.Bridge.SurjD.Native CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSporadicStandard.Fin76b.AutETable (mt ix tab ev)

@[expose] def invCodes (w : List ℕ) : List ℕ := (w.map fun c => c ^^^ 1).reverse

@[expose] def conjRel (y i : ℕ) (W : List ℕ) : List ℕ := [2 * y + 1, 2 * i, 2 * y] ++ invCodes W

@[expose] def czJRelCodes : List (List ℕ) :=
  czRelsJ ++ (List.range 6).map (fun i => conjRel 6 i (czWq.getD i [])) ++
    (List.range 6).map (fun i => conjRel 7 i (czWv.getD i [])) ++
    (List.range 6).map (fun i => conjRel 8 i (czWw.getD i []))

@[expose] def czJRelRels : List (List (ℕ × Bool)) :=
  czJRelCodes.map (fun r => substWord (natWord r)) ++
    [substWord (natWord [0, 0]) ++ invNatWord (RuAsm.ruZ0Word.map fun l => (l.1.val, l.2))]

@[expose] def czRelsJW : List (List (Fin 6 × Bool)) := czRelsJ.map (wordOfCodes 6)

abbrev czN : ℕ := 2048

@[expose] def czUnpack (P : ℕ) : Array ℕ := Array.ofFn (n := 128) fun i => (P >>> (7 * i.val)) % 128

@[expose] def czJCert : ArrCert :=
  ⟨czJCertP.pts.map czUnpack, czJCertP.edges, czJCertP.par, czJCertP.lab⟩

@[expose] def leftIdx (n : ℕ) (c : ArrCert) (k : ℕ) : Array ℕ :=
  tab n fun i => ix (c.edges.getD i #[]) k

@[expose] def tabRow (n : ℕ) (c : ArrCert) (L : Array (Array ℕ)) : ℕ → ℕ → Array ℕ
  | 0, _ => idA n
  | f + 1, a =>
    if a = 0 then idA n else compA n (L.getD (ix c.lab a) #[]) (tabRow n c L f (ix c.par a))

@[expose] def tabOf (n : ℕ) (c : ArrCert) (ngen : ℕ) : Array (Array ℕ) :=
  let L := (Array.range ngen).map (leftIdx n c)
  (Array.range n).map fun a => tabRow n c L n a

@[expose] def invOf (n : ℕ) (M : Array (Array ℕ)) : Array ℕ :=
  tab n fun a => ix (invCand n (M.getD a #[])) 0

@[expose] def gIdx (c : ArrCert) (k : ℕ) : ℕ := ix (c.edges.getD 0 #[]) k

@[expose] def letF (inv : Array ℕ) (t : List ℕ) (l : ℕ) : ℕ :=
  if l % 2 = 0 then t.getD (l / 2) 0 else ix inv (t.getD (l / 2) 0)

@[expose] def evW (M : Array (Array ℕ)) (inv : Array ℕ) (t : List ℕ) (w : List ℕ) : ℕ :=
  ev M (letF inv t) w

@[expose] def homVal (M : Array (Array ℕ)) (c : ArrCert) (t : List ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, a => if a = 0 then 0 else mt M (t.getD (ix c.lab a) 0) (homVal M c t f (ix c.par a))

@[expose] def homTab (n : ℕ) (M : Array (Array ℕ)) (c : ArrCert) (t : List ℕ) : Array ℕ :=
  tab n (homVal M c t n)

@[expose] def tableOK (n : ℕ) (c : ArrCert) (M : Array (Array ℕ)) (inv : Array ℕ) (gi : List ℕ) :
    Bool :=
  decide (c.pts.size = n) &&
    (List.range n).all (fun a => a == 0 || mt M (gi.getD (ix c.lab a) 0) (ix c.par a) == a) &&
    (List.range n).all fun a => decide (ix inv a < n) && mt M a (ix inv a) == 0

@[expose] def czJTab : Array (Array ℕ) := tabOf czN czJCert 6

@[expose] def czJInv : Array ℕ := invOf czN czJTab

@[expose] def czJGens : List ℕ := (List.range 6).map (gIdx czJCert)

@[expose] def czRels1 : List (List ℕ) := czRelsJ.filter fun r => r.all fun l => l < 4

@[expose] def czRels3 : List (List ℕ) :=
  czRelsJ.filter fun r => (r.all fun l => l < 8) && !(r.all fun l => l < 4)

@[expose] def czRels5 : List (List ℕ) := czRelsJ.filter fun r => !(r.all fun l => l < 8)

@[expose] def relsHold (M : Array (Array ℕ)) (inv : Array ℕ) (rs : List (List ℕ)) (t : List ℕ) :
    Bool :=
  rs.all fun r => evW M inv t r == 0

@[expose] def conjTuples (n : ℕ) (M : Array (Array ℕ)) (inv : Array ℕ) (gi : List ℕ) :
    List (List ℕ) :=
  (List.range n).map fun d => gi.map fun g => mt M (mt M (ix inv d) g) d

@[expose] def cubeInner (n : ℕ) (M : Array (Array ℕ)) (c : ArrCert) (gi : List ℕ)
    (conjT : List (List ℕ)) (kw : Array ℕ) (t : List ℕ) : Bool :=
  let phi := fun a => homVal M c t n (ix kw a)
  conjT.contains (gi.map fun g => phi (phi (phi g)))

@[expose] def rigidSearch (n : ℕ) (M : Array (Array ℕ)) (inv : Array ℕ) (c : ArrCert)
    (gi : List ℕ) : Bool :=
  let kq := homTab n M c (czWq.map (evW M inv gi))
  let kw := homTab n M c (czWw.map (evW M inv gi))
  let fix := (List.range n).filter fun a => ix kq a == a
  let d3 := (List.range n).filter fun a =>
    ix kq (ix kq a) == evW M inv [0, 0, a, ix kq a, 0, 0] (czWq.getD 3 [])
  let d5 := (List.range n).filter fun a =>
    ix kq (ix kq a) == evW M inv [0, 0, 0, 0, a, ix kq a] (czWq.getD 5 [])
  let conjT := conjTuples n M inv gi
  let sols := czSols.map fun s => s.map (evW M inv gi)
  ix kq (gi.getD 0 0) == gi.getD 0 0 && ix kq (gi.getD 1 0) == gi.getD 1 0 &&
    ix kq (gi.getD 2 0) == gi.getD 3 0 && ix kq (gi.getD 4 0) == gi.getD 5 0 &&
    fix.all fun a0 => fix.all fun a1 =>
      !relsHold M inv czRels1 [a0, a1, 0, 0, 0, 0] ||
      d3.all fun a2 =>
        !relsHold M inv czRels3 [a0, a1, a2, ix kq a2, 0, 0] ||
        d5.all fun a4 =>
          let t := [a0, a1, a2, ix kq a2, a4, ix kq a4]
          !(relsHold M inv czRels5 t && cubeInner n M c gi conjT kw t) || sols.contains t

@[expose] def czRigidCheck : Bool :=
  enumOK 128 czT128 czBase128 czJCert && tableOK czN czJCert czJTab czJInv czJGens &&
    relsHold czJTab czJInv czRelsJ czJGens &&
    rigidSearch czN czJTab czJInv czJCert czJGens

@[expose] def czHTarget (i : ℕ) : List ℕ := invCodes ((czHCodes.getD i []).drop 3)

@[expose] def letterTab (n : ℕ) (M : Array (Array ℕ)) (inv : Array ℕ) (gi : List ℕ)
    (K : Array (Array ℕ)) (l : ℕ) : Array ℕ :=
  if l < 12 then
    let g := if l % 2 = 0 then gi.getD (l / 2) 0 else ix inv (gi.getD (l / 2) 0)
    tab n fun a => mt M (mt M (ix inv g) a) g
  else if l % 2 = 0 then K.getD (l / 2 - 6) #[] else invCand n (K.getD (l / 2 - 6) #[])

@[expose] def identSearch (n : ℕ) (M : Array (Array ℕ)) (inv : Array ℕ) (c : ArrCert)
    (gi : List ℕ) : Bool :=
  let A := (List.range 6).map fun i => evW M inv gi (czHTarget i)
  let sols := czSols.map fun s => s.map (evW M inv gi)
  let gam := homTab n M c ((List.range 6).map fun i => evW M inv gi (c2JCodes.getD i []))
  let K := #[homTab n M c (czWq.map (evW M inv gi)), homTab n M c (czWv.map (evW M inv gi)),
    homTab n M c (czWw.map (evW M inv gi)), homTab n M c A]
  (List.range 4).all (fun s =>
    let x := evW M inv gi (czNormX.getD s [])
    (List.range 6).all fun i =>
      mt M (mt M (ix inv x) ((sols.getD s []).getD i 0)) x == A.getD i 0) &&
  relsHold M inv czRelsJ ((List.range 6).map fun i => evW M inv gi (c2JCodes.getD i [])) &&
  (List.range 4).all (fun s =>
    let s' := czClass2To1.getD s 0
    let al := homTab n M c (sols.getD (s + 4) [])
    decide (s' < 4) && (List.range 6).all fun i =>
      ix al (ix gam (gi.getD i 0)) == ix gam ((sols.getD s' []).getD i 0)) &&
  (List.range 4).all (fun j => isInvA n (K.getD j #[]) (invCand n (K.getD j #[]))) &&
  (czHCodes.drop 7).all (fun r =>
    let T := r.foldl (fun T l => compA n (letterTab n M inv gi K l) T) (idA n)
    gi.all fun g => ix T g == g) &&
  (List.range n).filter (fun a => gi.all fun g => mt M a g == mt M g a) ==
    [0, evW M inv gi [0, 0]]

@[expose] def czJIdentCheck : Bool :=
  enumOK 128 czT128 czBase128 czJCert && tableOK czN czJCert czJTab czJInv czJGens &&
    identSearch czN czJTab czJInv czJCert czJGens

end CFSG.ComponentClassification.GMS78.RuCz
