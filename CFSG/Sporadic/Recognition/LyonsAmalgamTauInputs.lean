module

public import CFSG.Sporadic.Recognition.LyonsAmalgamYInputs
public import CFSG.Sporadic.Recognition.LyonsAmalgamTrInputs
public meta import CFSG.Sporadic.Recognition.LyonsAmalgamYInputs
public meta import CFSG.Sporadic.Recognition.LyonsAmalgamTrInputs

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Tau

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def yEnum : Array Table × Array Nat × Array Nat :=
  CFSG.Sporadic.Recognition.LyonsSims.Ly1080.txyEnum

@[expose] def tEnum : Array Table := Id.run do
  let par := yEnum.2.1
  let lab := yEnum.2.2
  let mut out : Array Table := #[idT CFSG.Sporadic.Recognition.LyonsSims.Ly243.deg]
  for k in [1:par.size] do
    out := out.push (compT CFSG.Sporadic.Recognition.LyonsSims.Ly243.deg out[par[k]!]!
      CFSG.Sporadic.Recognition.LyonsSims.Ly243.txyTabs[lab[k]!]!)
  return out

@[expose] def yKeys : Std.HashMap UInt64 Nat :=
  (yEnum.1.toList.zipIdx).foldl (fun m p =>
    m.insert (hkey CFSG.Sporadic.Recognition.LyonsSims.Ly1080.deg p.1) p.2) {}

@[expose] def succTab : Array (Array Nat) :=
  yEnum.1.map fun x => (Array.range 5).map fun l =>
    yKeys.getD (hkey CFSG.Sporadic.Recognition.LyonsSims.Ly1080.deg
      (compT CFSG.Sporadic.Recognition.LyonsSims.Ly1080.deg x
        CFSG.Sporadic.Recognition.LyonsSims.Ly1080.txyTabs[l]!)) 0

@[expose] def tauOK : Bool :=
  mulTreeOK CFSG.Sporadic.Recognition.LyonsSims.Ly243.deg
    CFSG.Sporadic.Recognition.LyonsSims.Ly243.txyTabs tEnum yEnum.2.1 yEnum.2.2 &&
    hkeysDistinct CFSG.Sporadic.Recognition.LyonsSims.Ly243.deg tEnum.toList &&
    tEnum.size == yEnum.1.size && succTab.size == yEnum.1.size &&
    (List.range yEnum.1.size).all fun k => (List.range 5).all fun l =>
      let k' := succTab[k]![l]!
      k' < yEnum.1.size &&
        tblEq CFSG.Sporadic.Recognition.LyonsSims.Ly1080.deg yEnum.1[k']!
          (compT CFSG.Sporadic.Recognition.LyonsSims.Ly1080.deg yEnum.1[k]!
            CFSG.Sporadic.Recognition.LyonsSims.Ly1080.txyTabs[l]!) &&
        tblEq CFSG.Sporadic.Recognition.LyonsSims.Ly243.deg tEnum[k']!
          (compT CFSG.Sporadic.Recognition.LyonsSims.Ly243.deg tEnum[k]!
            CFSG.Sporadic.Recognition.LyonsSims.Ly243.txyTabs[l]!)

end CFSG.Sporadic.Recognition.LyonsSims.Tau
