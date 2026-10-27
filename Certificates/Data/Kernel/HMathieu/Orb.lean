module

public import CFSG.Quasithin.Background.HParabBase
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.HFixSylBase
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Parab

inductive KT where
  | leaf : KT
  | node : KT → Nat → KT → KT

@[expose] def KT.mem : KT → Nat → Bool
  | .leaf, _ => false
  | .node l k r, x => if x = k then true else if x < k then l.mem x else r.mem x

@[expose] def KT.ins : KT → Nat → KT
  | .leaf, x => .node .leaf x .leaf
  | .node l k r, x =>
    if x = k then .node l k r else if x < k then .node (l.ins x) k r else .node l k (r.ins x)

structure OT where
  front : List (List Nat)
  back : List (List Nat)
  cnt : Nat
  tree : KT

@[expose] def otRound (cs : List (List Nat)) (b : List Nat) (t : OT) (g : Nat) : OT :=
  if t.tree.mem (maskKey (b.map (actM (cs.getD g [])))) then t
  else ⟨t.front, b.map (actM (cs.getD g [])) :: t.back, t.cnt + 1,
    t.tree.ins (maskKey (b.map (actM (cs.getD g []))))⟩

@[expose] def orbTwin (cs : List (List Nat)) : Nat → OT → Nat
  | 0, t => t.cnt
  | f + 1, ⟨b :: fr, bk, c, tr⟩ =>
    orbTwin cs f ((List.range cs.length).foldl (otRound cs b) ⟨fr, bk, c, tr⟩)
  | f + 1, ⟨[], bk, c, tr⟩ =>
    match bk.reverse with
    | [] => c
    | b :: fr => orbTwin cs f ((List.range cs.length).foldl (otRound cs b) ⟨fr, [], c, tr⟩)

@[expose] def orbCount (cs : List (List Nat)) (d : List Nat) (N : Nat) : Nat :=
  orbTwin cs (N + 1) ⟨[d], [], 1, KT.leaf.ins (maskKey d)⟩

end CFSG.KC.HMathieu

end
