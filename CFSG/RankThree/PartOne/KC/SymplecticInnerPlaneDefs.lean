module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeBlocks

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

section Defs

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def spBlockImage (x : StatedSp r K) (h : K[X]) :
    Subgroup (StatedProj (StatedSp r K)) :=
  ((specialBlock (spForm r K) (spLin r K x) h).comap (spLin r K)).map (proj r K)

@[expose] noncomputable def spFixedFactor (x : StatedSp r K) : Subgroup (StatedSp r K) :=
  spSupported x {X - 1}

@[expose] noncomputable def spFixedDim (x : StatedSp r K) : ℕ :=
  finrank K (primaryComponent (spEnd x) (X - 1))

@[expose] def SpFixedListed (x : StatedSp r K) : Prop :=
  2 ≤ spFixedDim x ∧ ¬ (spFixedDim x = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3))

open scoped _root_.Classical in
@[expose] noncomputable def spFixedLayerImage (x : StatedSp r K) :
    Subgroup (StatedProj (StatedSp r K)) :=
  if SpFixedListed x then
    (if spFixedDim x = 4 ∧ Nat.card K = 2 then ⁅spFixedFactor x, spFixedFactor x⁆
      else spFixedFactor x).map (proj r K)
  else ⊥

@[expose] noncomputable def spListedProduct (x : StatedSp r K) :
    Subgroup (StatedProj (StatedSp r K)) :=
  (⨆ h : primaryFactors (spEnd x), ⨆ (_ : (h : K[X]) ≠ X - 1 ∧
      2 ≤ primaryMultiplicity (spEnd x) (h : K[X])), spBlockImage x (h : K[X])) ⊔
    spFixedLayerImage x

@[expose] noncomputable def spLocalCore (p : ℕ)
    (B : Subgroup (MulAut (StatedProj (StatedSp r K)))) (a : StatedProj (StatedSp r K)) :
    Subgroup (MulAut (StatedProj (StatedSp r K))) :=
  CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
    (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (StatedProj (StatedSp r K)))))

end Defs

end CFSG.RankThree.PartOne
