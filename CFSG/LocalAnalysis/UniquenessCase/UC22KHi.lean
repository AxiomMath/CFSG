module

public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi8d
public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi2c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22o

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22k_c118_U (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h118 : R118W D)
    (c : Ctx22c D Ch) : C118 D ⊥ D.U :=
  h118 D.U (uc22p22c_hyp11 D (uc22p22o_inCalW_U_of_not_isTI D hx h61 c.hU) c.hU)

theorem uc22k_Hi_exists (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hx : DataExt D) (h61 : UC6.R6_1 D) (h640 : UC6.R6_40_1 D) (h118 : R118W D) :
    H1930 D → ∀ c : Ctx22c D Ch, ∀ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)), NbarSplit D Nb →
      ∀ i, ∃ H : Subgroup G, HiPkgK D (Nb i) H := by
  intro hH c m Nb hNb i
  have h118U := uc22k_c118_U D Ch hx h61 h118 c
  obtain ⟨n, hn, hn2⟩ := h51 hH c m Nb hNb i
  have hn1 : 1 ≤ n := by
    obtain ⟨F, _, _, hF, -⟩ := hn
    exact P22y.one_le_of_card hF
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · obtain rfl : n = 1 := by omega
    exact uc22k_Hi_exists_two D Ch h2 h3 h51 h640 h118U hH c hNb i hn
  · exact uc22k_Hi_exists_eight D Ch h2 h3 h51 h640 h118U hH c hNb i hn hge

end CFSG.LocalAnalysis.UniquenessCase.UC22
