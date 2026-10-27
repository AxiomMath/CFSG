module

public import CFSG.Quasithin.MS93.S34DAsm
public import CFSG.Quasithin.EmptyFaithful.SzMSWConcl

public section

namespace CFSG.Quasithin.SzMSW

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S34D

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem ms93ConclASW_of_critDist_eq_two (h32 : S32) (h36 : S36) (h37 : S37) (h18 : S18)
    (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 2) : MS93ConclASW M T L := by
  obtain ⟨h36a, h36b⟩ := h36 G M T L h hb
  by_cases hVU : Vq M L = Uq M T L
  swap
  · have hD := h36a.resolve_left hVU
    exact MS93ConclASW.of_case5 hD.2.1.le (h18 G M T L h hb hVU hD)
  have hVX : Vq M L ≤ Xq M := hVU ▸ h.Uq_le_Xq
  rcases h36b with hUD | ⟨k, hk⟩ | hii
  ·
    have hUZ : Uq M T L ⊓ Zq M L = ⊥ := by rw [h.Uq_inf_Zq, ← h.Uq_inf_Dq, hUD]
    obtain ⟨-, -, h32c⟩ := h32 G M T L h
    rcases h32c with ⟨-, -, n, F, hF, hFt, α, hcard, hsurj, hnat⟩ | ⟨-, -, hU, hA6⟩ |
        ⟨hX, -, n, F, hF, hFt, α, hcard, hsurj, hnat⟩ | ⟨-, hcard2, -, -⟩ |
        ⟨-, -, -, α, hsurj, hnat⟩ | ⟨k, hvi⟩ | ⟨-, -, ⟨hU, hG2⟩, -⟩
    · refine MS93ConclASW.of_case4 ⟨hVX, n, F, hF, hFt, α, hcard, hsurj, ?_⟩
      rw [hVU]
      exact hnat
    · refine MS93ConclASW.of_case6 ⟨hVX, ?_⟩
      rw [hVU]
      exact ⟨hU, hA6⟩
    · refine MS93ConclASW.of_case5 hX.le ⟨n, F, hF, hFt, α, hcard, hsurj, ?_⟩
      rw [hVU]
      exact hnat
    · rw [inf_comm, hUZ, Subgroup.card_bot] at hcard2
      exact absurd hcard2 (by norm_num)
    · refine MS93ConclASW.of_case4 ⟨hVX, 1, ZMod 2, inferInstance, inferInstance, α,
        by rw [ZMod.card, pow_one], hsurj, ?_⟩
      rw [hVU]
      exact hnat
    · rw [h.Uq_inf_Zq] at hvi
      rcases case2_or_case3_of_sp4 h37 h hb hVU hvi with h2 | h3
      · exact MS93ConclASW.of_case2 h2
      · exact MS93ConclASW.of_case3 h3
    · refine MS93ConclASW.of_case10 ⟨hVX, ?_⟩
      rw [hUZ, intSub_bot] at hG2
      rw [hVU]
      exact ⟨hU, hG2⟩
  ·
    rw [h.Uq_inf_Dq] at hk
    rcases case2_or_case3_of_sp4 h37 h hb hVU hk with h2 | h3
    · exact MS93ConclASW.of_case2 h2
    · exact MS93ConclASW.of_case3 h3
  ·
    obtain ⟨⟨α, hsurj, hnat⟩, hcard, hTQ, hcomm, hX, hSyl⟩ := hii
    have hUDM := h.Uq_inf_Dq_eq_of_card hcard
    refine MS93ConclASW.of_case8 ?_
    unfold MS93Case8
    rw [hVU, ← hUDM]
    refine ⟨⟨α, hsurj, hnat⟩, hcard, hTQ, hcomm, h.Uq_inf_Dq, rfl, hX, fun S hS => ?_⟩
    rw [hSyl S hS, hUDM]

end CFSG.Quasithin.SzMSW
