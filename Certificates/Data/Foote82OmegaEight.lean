module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeData
public import CFSG.CGT.Harada80.OmegaCodes
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.CGT.Foote82.OmegaEight

open CFSG.EvenSmallLie.OmegaEightMinus CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.CGT.Harada80

@[expose] def transArr (c : ℕ) : Array ℕ :=
  Array.ofFn (n := 136) fun i => nsIdx[transNat c nsArr[i.val]!]!

@[expose] def prodArr (cs : List ℕ) : Array ℕ :=
  cs.foldr (fun c t => compA 136 (transArr c) t) (idA 136)

@[expose] def eichRefl : List (List ℕ) :=
  [[36, 37, 53, 52], [36, 38, 46, 44], [9, 11, 43, 41], [9, 13, 29, 25], [68, 64], [132, 128],
    [196, 192], [96, 64], [160, 128], [224, 192]]

@[expose] def witTypes : List ℕ := [0, 1, 2, 4]

@[expose] def witWords : List (List ℤ) := [[4, 18], [2, 14], [1, 8], [4, 9]]

@[expose] def qLinkCheck (_ : Unit := ()) : Bool :=
  (List.range 256).all fun c =>
    (decide (CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 c) ≠ 0) == qNat c) &&
      (List.range 136).any fun j => qNat (nsArr[j]! ^^^ c)

@[expose] def reflLinkCheck (_ : Unit := ()) : Bool :=
  (List.range 136).all fun j => (List.range 256).all fun x =>
    reflCode 3 nsArr[j]! x == transNat nsArr[j]! x

@[expose] def autLevels (_ : Unit := ()) : Array Level :=
  rawLevels 136 autS (autBase.map Fin.val).toArray

@[expose] def transMemCheck (_ : Unit := ()) : Bool :=
  let lv := autLevels ()
  (List.range 136).all fun j => siftA 136 lv (autBase.map Fin.val).toArray 0 (transArr nsArr[j]!)

@[expose] def eichCheck (_ : Unit := ()) : Bool :=
  (List.range 10).all (fun i =>
    let cs := eichRefl.getD i []
    decide (cs.length % 2 = 0) && cs.all (fun c => decide (c < 256) && qNat c) &&
      eqA 136 genArrs[i]! (prodArr cs)) &&
    eqA 136 genArrs[10]! (transArr 64)

@[expose] def typeCheck (_ : Unit := ()) : Bool :=
  (List.range 4).all fun k =>
    let y := mainArrs.getD (witTypes.getD k 0) #[]
    let g := omegaW (witWords.getD k [])
    let z := compA 136 y (conjArr g y)
    isInvA 136 g (invCand 136 g) && eqA 136 (powArr z 12) (idA 136) &&
      !eqA 136 (powArr z 2) (idA 136) && !eqA 136 (powArr z 3) (idA 136)

@[expose] def reflRepCheck (_ : Unit := ()) : Bool :=
  eqA 136 (mainArrs.getD 3 #[]) (transArr 64)

end CFSG.CGT.Foote82.OmegaEight
