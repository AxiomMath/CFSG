module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBCDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

@[expose] def ggARoots (m : ℕ) : Set (GGBCV m) := {v | ggBCWt v = 2 ∧ ∑ i, v i = 0}

@[expose] def ggARootsLam1 (m : ℕ) [NeZero m] : Set (GGBCV m) := {v | v ∈ ggARoots m ∧ v 0 = 0}

@[expose] def ggAType1 {m : ℕ} (z : GGBCV m) : Prop :=
  ∃ c : ZMod 3, c ≠ 0 ∧ ∃ i, z i = -c ∧ ∀ j, j ≠ i → z j = c

@[expose] def ggAType4 {m : ℕ} (z : GGBCV m) : Prop :=
  (∀ i, z i ≠ 0) ∧ (Finset.univ.filter fun i => z i = 1).card = 4 ∧
    (Finset.univ.filter fun i => z i = -1).card = 4

@[expose] def ggDRoots (n : ℕ) : Set (GGBCV n) := {v | ggBCWt v = 2}

@[expose] def ggDRootsLam1 (n : ℕ) [NeZero n] : Set (GGBCV n) := {v | ggBCWt v = 2 ∧ v 0 = 0}

end CFSG.StandardType

end
