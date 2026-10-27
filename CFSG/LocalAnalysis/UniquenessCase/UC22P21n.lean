module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yh
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22o

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def S22_6Hat (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, ∀ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)),
    NbarSplit D Nb → Cl22_6Hat D Nb

theorem uc22p21n_s22_6hat_of (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (h61 : UC6.R6_1 D) (hX : DataExt D) (h119 : R119W D) (h1110 : R1110W D)
    (hsig3 : 3 < CFSG.Open.pRank 3 D.M → 3 ∈ D.sig) : S22_6Hat D Ch := by
  intro hH c m Nb hNb
  exact uc22p22yh_s22_6hat_of D Ch h2 h3 h51 h61 hX h119 h1110
    (uc22p22o_inCalW_U_of_not_isTI D hX h61 c.hU) hsig3 hH c m Nb hNb

end CFSG.LocalAnalysis.UniquenessCase.UC22
