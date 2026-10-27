module

public import CFSG.RankThree.PartOne.S12.Sec12Three

public section

namespace CFSG.RankThree.PartOne

open scoped commutatorElement

theorem node124b_of_inputs (h107 : InSec10Seven) (h109 : InSec10Nine) (h122 : Node122)
    (hKF : KF123) : Node124b := by
  intro G _ _ p A c L E h hZ
  rcases Sec12Hyp.table123_hyp h107 h109 h122 h with ⟨hG, -⟩ | ⟨hS, hT⟩
  · exact absurd hZ hG.center_pPrime
  · obtain ⟨-, -, hweyl, -, -, hlat⟩ := (hKF G p L A E).2 hT
    have hlat := hlat rfl
    have hcL := Sec12Three.comm_c_L h
    have hc5 : c ^ 5 = 1 := by
      have := Sec12Three.pow_eq_one_of_mem_A h h.c_mem
      rwa [hS.p_eq] at this
    have hnt : torusImage E L ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot _).1 (Sec12Three.nontrivial_of_rowWeylIso hweyl)
    rcases hlat _ (Sec12Three.commutator_le_left E L) (Sec12Three.torusInvariant_commutator E L)
      with h0 | hc | hE
    · exact absurd h0 (Sec12Three.commutator_ne_bot_of_moved
        (Sec12Three.exists_moved_of_torusImage_ne_bot hnt))
    · exact absurd (hc ▸ hS.center_eq ▸ le_rfl)
        (Sec12Three.not_commutator_le_zpowers_of_perm_five hc5 hcL hweyl)
    · exact hE

end CFSG.RankThree.PartOne
