module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588B6a
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588B3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

open CFSG.Sporadic.Schreier.Tits

variable {G : Type} [Group G] [Finite G] {Dat : Data G}


theorem c623_of_tits (hK : UCK.K322) (m : Mz614 Dat) (h67 : R6_7 Dat)
    (h69 : R6_9 Dat) (h620 : m.C620) (hr : m.r = 5)
    (hL : IsoLie ↥m.L .tits) : m.C623 := by
  classical
  by_contra hne
  obtain ⟨T⟩ := exists_titsSetup m h620 hr hL
  have h621 : m.C621 := c621_of_titsSetup T h620 hr
  have hs2 : 2 ^ 2 % m.r = m.r - 1 := by rw [hr]; norm_num
  obtain ⟨Z₂, Z₃, hZ₂L, hZ₃L, hZ₂c, hZ₃c, hZ₂₃, horb, h₂, h₃⟩ :=
    m.exists_pair_of_k322 hK h69 h620 h621 hr (T.y_mem h620) T.y_conj hs2 hne
  have hne₂ : Z₂ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hZ₂c
    exact m.hr.one_lt.ne hZ₂c
  have hne₃ : Z₃ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hZ₃c
    exact m.hr.one_lt.ne hZ₃c
  have hn2 := m.map_conj_sq_pair h620 hZ₂L hZ₃L hne₂ hne₃ hZ₂₃ horb h₂ h₃ (T.n_mem h620)
  obtain ⟨hY1, hY2⟩ := T.map_le_plane hZ₂L
  exact T.not_normalizes hY1 (by rw [hY2, hZ₂c, hr]) (T.map_normalized hZ₂L hn2)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
