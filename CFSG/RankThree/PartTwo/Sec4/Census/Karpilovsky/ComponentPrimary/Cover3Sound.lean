module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Sporadic.Recognition.CoverRecipeCube
public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.LieType.Multipliers
  CFSG.Blueprint CFSG.Sporadic.Recognition.CoverRecipe
open scoped Matrix

@[expose] def ofCodes (m : ℕ) [NeZero m] (c : List ℕ) : List (Fin m × Bool) :=
  c.map fun x => (Fin.ofNat m (x / 2), decide (x % 2 = 0))

section Words

variable {V : Type} (D : Cover3Data V) [NeZero D.m]

@[expose] def _root_.CFSG.SectionRank.Native.Cover3Data.rels : List (List (Fin D.m × Bool)) := D.relCodes.map (ofCodes D.m)

@[expose] def _root_.CFSG.SectionRank.Native.Cover3Data.ordF (i : Fin D.m) : ℕ := D.ord.getD i.val 0

@[expose] def _root_.CFSG.SectionRank.Native.Cover3Data.comm (i : Fin D.m) :
    List (List (Fin D.m × Bool) × List (Fin D.m × Bool)) :=
  (D.commCodes.getD i.val []).map fun p => (ofCodes D.m p.1, ofCodes D.m p.2)

@[expose] def _root_.CFSG.SectionRank.Native.Cover3Data.cwF (i : Fin D.m) : List (Fin D.m × Bool) :=
  if D.ordF i = 0 then commWords (D.comm i) else [(i, true)]

@[expose] def _root_.CFSG.SectionRank.Native.Cover3Data.cover : List (List (Fin D.m × Bool)) :=
  cover₃Words D.rels D.cwF D.ordF

end Words

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
