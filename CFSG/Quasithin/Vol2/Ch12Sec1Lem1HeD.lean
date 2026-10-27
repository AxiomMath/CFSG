module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeC
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def HeInspLieTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ f : ℕ,
      (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 2 f) ∨
      (1 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 f) ∨
      (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 2 f) ∨
      (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ SuzukiModel X 2 f)) ∨
      ReeTitsModel X .Tits 2 1) →
    ∀ m : ℕ, (m = 3 ∨ m = 4) → ¬ HeInspCfg X m

namespace Sec1211He

theorem lem1211HeInsp_of
    (hAlt : HeInspRankAlt) (hOdd : HeInspRankOdd) (hSpor : HeInspRankSpor)
    (hEight : HeInspRankEight) (hE64 : HeInspE64) (hRu : HeInspRu) (hJ4 : HeInspJ4)
    (hLie : HeInspLieTwo) : Lem1211HeInsp := by
  intro G _ _ hG hna hqtke H K Y W₁ W₂ m t hH hK hm hYK hWY hWW hE hWC C₁ C₂ hk hd htK htY htW hR
  have hloc : LocalSQTK G := fun P hP => by
    have h := sqtkGroup_of_pCoreOf_ne_bot hqtke hG hna hP
    exact ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mpr h.1, h.2⟩
  have hlist := Ch1.sqtkSimpleList_component hloc hH hK
  have hcfg := heInspCfg_of hYK hWY hWW hE hWC C₁ C₂ hk hd htK htY htW hR
  rcases hlist with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨p, hp, hp2, hodd⟩ | h3 | ⟨n, hn, hL⟩ | ⟨s, hs, ⟨e⟩⟩
  · exact not_heInspCfg_of_twoRankLtSix (twoRankLtSix_of_mulEquiv e (hAlt.1 n h5 h8)) hm hcfg
  · exact not_heInspCfg_of_twoRankLtSix (hOdd _ p hp hp2 hodd) hm hcfg
  · exact hLie _ h3 m hm hcfg
  · rcases hn with rfl | rfl
    · exact not_heInspCfg_of_twoRankLtSix (hAlt.2 _ hL) hm hcfg
    · rcases hm with rfl | rfl
      · exact hE64.1 _ hL hcfg
      · exact not_heInspCfg_of_twoRankLtEight (hEight.1 _ hL) hcfg
  · have hsix : ∀ s' : TauCeti.SporadicName, s' = s → (s' = .M11 ∨ s' = .M12 ∨ s' = .M22 ∨
        s' = .M23 ∨ s' = .J1 ∨ s' = .J2 ∨ s' = .HS) → False := fun s' hs' h7 =>
      not_heInspCfg_of_twoRankLtSix (twoRankLtSix_of_mulEquiv e (hs' ▸ hSpor s' h7)) hm hcfg
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsix _ rfl (Or.inl rfl)
    · exact hsix _ rfl (Or.inr (Or.inl rfl))
    · exact hsix _ rfl (Or.inr (Or.inr (Or.inl rfl)))
    · exact hsix _ rfl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · rcases hm with rfl | rfl
      · exact hE64.2.1 (heInspCfg_of_mulEquiv e hcfg)
      · exact not_heInspCfg_of_twoRankLtEight (twoRankLtEight_of_mulEquiv e hEight.2.1) hcfg
    · exact hsix _ rfl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact hsix _ rfl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · rcases hm with rfl | rfl
      · exact hJ4.1 (heInspCfg_of_mulEquiv e hcfg)
      · exact hJ4.2 (heInspCfg_of_mulEquiv e hcfg)
    · exact hsix _ rfl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    · rcases hm with rfl | rfl
      · exact hE64.2.2 (heInspCfg_of_mulEquiv e hcfg)
      · exact not_heInspCfg_of_twoRankLtEight (twoRankLtEight_of_mulEquiv e hEight.2.2.1) hcfg
    · rcases hm with rfl | rfl
      · exact hRu (heInspCfg_of_mulEquiv e hcfg)
      · exact not_heInspCfg_of_twoRankLtEight (twoRankLtEight_of_mulEquiv e hEight.2.2.2) hcfg

end Sec1211He

end CFSG.Quasithin.H13
