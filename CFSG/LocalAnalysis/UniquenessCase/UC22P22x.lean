module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)

variable {G : Type} [Group G] [Finite G]

@[expose] def proofIi (D : Data G) (Ni : Subgroup G) : Subgroup G := ⁅⁅D.U, proofN D⁆, Ni⁆

@[expose] def proofEiHat (D : Data G) (Ni : Subgroup G) : Subgroup G := ⁅proofIi D Ni, jOf D.T⁆

@[expose] def Cl22_6Hat (D : Data G) {m : ℕ} (Nb : Fin m → Subgroup (MBar D.M D.U)) : Prop :=
  ∀ i, normalizer (proofEiHat D (preN D (Nb i)) : Set G) ≤ D.M

end CFSG.LocalAnalysis.UniquenessCase.UC22
