module

public import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.Sporadic.Bridge.Common
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InB

open CFSG.Sporadic.GLQ CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.Fi23GPL.Native

@[expose] def Fi23ImgFacts {G : Type*} [Group G] (U V : G) : Prop :=
  (∀ k < 10, signedWord U V (imgWords ())[k]! ^ 2 = 1) ∧
    (∀ v ∈ rels (), wordProd (fun k => signedWord U V (imgWords ())[k]!) v = 1) ∧
    signedWord U V (imgWords ())[0]! ≠ 1

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InB
