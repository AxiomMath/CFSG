module

public import CFSG.Quasithin.Vol2.KGFactInspE16Base
public import CFSG.Quasithin.Vol2.KGFactInspL2U3
public import CFSG.Quasithin.EmptyFaithful.R3c3Rank
public import CFSG.Quasithin.EmptyFaithful.R3c3Lie
public import CFSG.Quasithin.EmptyFaithful.R3c3Spor
public import CFSG.Quasithin.Vol2.KGFactInsp4316Props

public section

namespace CFSG.Quasithin.H13.KGInsp4316

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedLieTag StatedProj StatedSU
  StatedScalars
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups

namespace E16Cfg

variable {X : Type} [Group X] [Finite X] {S R K : Subgroup X}

theorem false_of_pRank_three
    (h : E16Cfg S R K) (h3 : CFSG.Open.pRank 3 S ≤ 1) : False := by
  have hc := h.cfg
  have hRS := h.R_le_S
  have h3' := false_of_two_le_pRank_three h3
  rcases h.list with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p, hp, hp2, ⟨f, -, hm⟩ | hm | hm⟩ |
      ⟨⟨f, ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨hf, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, -, hm⟩ |
        ⟨-, -, hm⟩⟩ | hT⟩ | ⟨n, hn, hm⟩ | ⟨s, hs, ⟨e⟩⟩
  · by_cases h5 : n = 5
    · subst h5
      have h16 := h.sixteen_dvd
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin] at h16
      exact absurd h16 (by decide)
    · exact h3' (CFSG.Quasithin.R3c3.two_le_pRank_three_alt (by omega) e)
  · exact hc.false_of_psl2 hRS hm
  · exact h.false_of_pRank_two_le (pRank_two_le_two_of_psl3_odd hp hp2 hm)
  · exact h.false_of_pRank_two_le (pRank_two_le_two_of_psu3_odd hp hp2 hm)
  · exact hc.false_of_psl2 hRS hm
  · obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' f
    · exact h3' (CFSG.Quasithin.R3c3.two_le_pRank_three_isPSL_three_two_even ⟨k, two_mul k⟩ hm)
    · exact not_five_dvd_card_psl3_of_odd ⟨k, rfl⟩ hm h.five_dvd
  · exact hc.false_of_psu3_two hRS hf hm
  · exact h3' (CFSG.Quasithin.R3c3.two_le_pRank_three_isPSp_two hm)
  · exact h3' (CFSG.Quasithin.R3c3.two_le_pRank_three_isG2 hm)
  · exact h3' (CFSG.Quasithin.R3c3.two_le_pRank_three_is3D4 hm)
  · exact h3' (CFSG.Quasithin.R3c3.two_le_pRank_three_is2F4 hm)
  · exact hc.false_of_isSz hm
  · exact h3' (CFSG.Quasithin.R3c3.two_le_pRank_three_isTits hT)
  · exact h3' (CFSG.Quasithin.R3c3.two_le_pRank_three_isPSL_two_one hn hm)
  · by_cases hJ : s = .J1
    · subst hJ
      have h16 := h.sixteen_dvd
      have hc : Nat.card (NativeSporadic.Carrier .J1) = 175560 := CFSG.Sporadic.J1.card_J1
      rw [Nat.card_congr e.toEquiv, hc] at h16
      exact absurd h16 (by decide)
    · have hs' : CFSG.QuasithinUnique.Ch1.IsLemma115SporadicName s := by
        unfold CFSG.QuasithinUnique.Ch1.IsLemma115SporadicName
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all
      exact h3' (CFSG.Quasithin.R3c3.two_le_pRank_three_of_lemma115SporadicName hs' e)

end E16Cfg

theorem insp4316E16m_holds :
    Insp4316E16m := by
  intro X _ _ S R K hN hsimp hnc hlist hC F _ _ hF hle hperf hKN hNK hchi h3 hcore helem hcard _
  exact (E16Cfg.false_of_pRank_three ⟨hN, hsimp, hnc, hlist, hC, hle, hperf, hKN, hNK,
    ⟨F, inferInstance, inferInstance, hF, hchi⟩, hcore, helem, hcard⟩ h3).elim

end CFSG.Quasithin.H13.KGInsp4316
