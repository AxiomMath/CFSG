module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Defs
public import CFSG.LieType.Ree.LargeReeInvolutionFusion

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def octBlk (i : Fin F4.fixedWeylOrder) (j : Fin F4.fixedOrbitCount) :
    Set (Fin F4.tag.rank → ℤ) :=
  (F4.fixedRelElt i • ·) '' F4.fixedOrbitRoots j

@[expose] def octPos (k : ℤ) : Set (Fin F4.tag.rank → ℤ) :=
  if k = 1 then octBlk ⟨0, by decide⟩ ⟨1, by decide⟩
  else if k = 2 then octBlk ⟨2, by decide⟩ ⟨0, by decide⟩
  else if k = 3 then octBlk ⟨4, by decide⟩ ⟨1, by decide⟩
  else if k = 4 then octBlk ⟨6, by decide⟩ ⟨0, by decide⟩
  else if k = 5 then octBlk ⟨5, by decide⟩ ⟨1, by decide⟩
  else if k = 6 then octBlk ⟨3, by decide⟩ ⟨0, by decide⟩
  else if k = 7 then octBlk ⟨1, by decide⟩ ⟨1, by decide⟩
  else if k = 8 then octBlk ⟨0, by decide⟩ ⟨0, by decide⟩
  else ∅

@[expose] def octBlock (k : ℤ) : Set (Fin F4.tag.rank → ℤ) :=
  if 0 < k then octPos k else Neg.neg '' octPos (-k)

@[expose] def octLab (k : ℤ) : CFSG.LocalAnalysis.EvenBN.TwoF4.Idx :=
  if k = 1 then .i1 else if k = 2 then .i7 else if k = 3 then .i6 else if k = 4 then .i10
  else if k = 5 then .i5 else if k = 6 then .i9 else if k = 7 then .i4 else .i3

section Data


variable (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)

@[expose] def octRoot (k : ℤ) : Subgroup (Gm K a) :=
  (largeReeBlockGroup K a (octBlock k)).subgroupOf (F4.reeGamma K a)

@[expose] def octH : Subgroup (Gm K a) :=
  (F4.reeFixedTorus K a).subgroupOf (F4.reeGamma K a)

@[expose] def octR1 : Gm K a := ⟨weylTwo K, weylTwo_mem⟩

@[expose] def octR2 : Gm K a := ⟨weylOne K, weylOne_mem⟩

end Data

end CFSG.Quasithin.H13.F431.TwoF4
