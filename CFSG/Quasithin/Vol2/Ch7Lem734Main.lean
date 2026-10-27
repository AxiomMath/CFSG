module

public import CFSG.Quasithin.Vol2.Ch7Lem734Mod
public import CFSG.Quasithin.Vol2.Ch7Lem734Rows
public import CFSG.Quasithin.Vol2.Ch7Lem741
public import CFSG.Quasithin.Vol2.Ch7Lem734E22

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem rows_cases [IsMulCommutative ↥(fsuV T I)] (hrow : Rows7_1_1 T L I) :
    (Row711SU3 T L I ∨ Row711Sz T L I ∨ (∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M12 T L I ∨
        Row711M22Hat T L I ∨ Row711M22Code T L I ∨ Row711M22Cocode T L I ∨
        Row711M23Code T L I ∨ Row711M23Cocode T L I ∨ Row711M24Code T L I ∨
        Row711M24Cocode T L I ∨ (∃ n : ℕ, Row711SL3Pair T L I n) ∨ Row711Sp4Pair T L I ∨
        Row711S7Pair T L I) ∨
      Row711L3Wreath T L I ∨ ∃ n : ℕ, Row711OmegaPlus T L I n := by
  rcases hrow with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h)))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl h))))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

omit [Finite G] in
theorem one_le_of_row711SL3Pair [IsMulCommutative ↥(fsuV T I)] {n : ℕ}
    (hrow : Row711SL3Pair T L I n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · obtain ⟨-, K, _, _, hK, -⟩ := hrow
    have : (1 : ℕ) < Nat.card K := Finite.one_lt_card
    rw [hK, pow_zero] at this
    exact absurd this (lt_irrefl 1)
  · exact h

theorem stmt7_3_4_of
    (hE22 : E2.E22StatementC) (h331 : Stmt3_3_1) (h4414 : Stmt4_4_14)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5)
    (h63 : ASInputs.AS_E_6_3) (hin : Input8_1_2) (h711 : Stmt7_1_1)
    (h711n : Stmt7_1_1_normal) (h771 : Stmt7_7_1)
    (hwr : Stmt7_3_4_E336_wreath) (hSp4 : Stmt7_2_1_Sp4Pair) (hS7 : Stmt7_2_1_S7)
    (nSU3 : Stmt7_3_4_nPrime_SU3) (nSz : Stmt7_3_4_nPrime_Sz) (nL3 : Stmt7_3_4_nPrime_L3Nine)
    (nMat : Stmt7_3_4_nPrime_Mathieu) (nSL3 : Stmt7_3_4_nPrime_SL3Pair)
    (nSL1 : Stmt7_3_4_nPrime_SL3One) (nSp4 : Stmt7_3_4_nPrime_Sp4Pair)
    (nA6 : Stmt7_3_4_nPrime_A6Pair) (nS7 : Stmt7_3_4_nPrime_S7Pair)
    (nWr : Stmt7_3_4_nPrime_L3Wreath) (mSz : Stmt7_2_1_m_Sz) (mL3 : Stmt7_2_1_m_L3Nine)
    (mMat : Stmt7_2_1_m_Mathieu) (mSL3 : Stmt7_2_1_m_SL3Pair) (mWr : Stmt7_2_1_m_L3Wreath) :
    Stmt7_3_4 := by
  intro G _ _ T L I hyp h731 hV
  have hmod := stmtFSUModule_of_eight h3228
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hk : IsNPrime721 T L I (nPrime (autI hV ⊤)) := by
    intro hc
    refine ⟨fun n hn h => nSU3 G T L I hyp hV hN hNM hc n hn h,
      fun n h => nSz G T L I hyp hV hN hNM hc n h,
      fun n h => nL3 G T L I hyp hV hN hNM hc n h,
      fun h => nMat G T L I hyp hV hN hNM hc h, fun n h => ?_,
      fun n hn htw h => nSp4 G T L I hyp hV hN hNM hc htw n hn h,
      fun htw h => nA6 G T L I hyp hV hN hNM hc htw h,
      fun h => nS7 G T L I hyp hV hN hNM hc h, fun h => nWr G T L I hyp hV hN hNM hc h⟩
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have h1 : n = 1 := le_antisymm (by omega) (one_le_of_row711SL3Pair h)
      subst h1
      exact nSL1 G T L I hyp hV hN hNM hc h
    · exact nSL3 G T L I hyp hV hN hNM hc n hn h
  obtain ⟨hc, hrow⟩ := h711 G T L I hyp
  have hstr : IsTISetUnder (fsuV T I) (fsuM T L) ∧
      ∀ H : Subgroup G, IsHStar T (fsuM T L) H → 1 < E1.nParam H →
        H ⊓ fsuM T L = H ⊓ Subgroup.normalizer (fsuV T I : Set G) ∧
          H ⊓ fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤
            pCoreOf 2 (H ⊓ fsuM T L) := by
    by_cases hTL : T ≤ Subgroup.normalizer (L : Set G)
    · exact ⟨isTISetUnder_of_le_normalizer h325 hyp.fsu hTL,
        local_structure_of_normal h4414 hC58 h317 h37 h38 h39 h3228 h325 hyp hTL⟩
    · rcases rows_cases hrow with h | h | ⟨n, h⟩
      · exact absurd (h711n G T L I hyp hc h) hTL
      · exact hwr G T L I hyp hV hN hNM hc h
      · exact absurd h (h731 hc n)
  have hE := hypE61_of_ti h37 h38 h39 hmod h3228 hyp hstr.1
  have hE336 := hypE336_of_hypE61 hE hstr.2
  have hnm : ¬ Row711SU3 T L I → nPrime (autI hV ⊤) < mParam (autI hV ⊤) ∧
      (2 < mParam (autI hV ⊤) ∨ Row711SL3Pair T L I 1) := by
    intro hU
    have hmat : (Row711M12 T L I ∨ Row711M22Hat T L I ∨ Row711M22Code T L I ∨
        Row711M22Cocode T L I ∨ Row711M23Code T L I ∨ Row711M23Cocode T L I ∨
        Row711M24Code T L I ∨ Row711M24Cocode T L I) →
        nPrime (autI hV ⊤) < mParam (autI hV ⊤) ∧
          (2 < mParam (autI hV ⊤) ∨ Row711SL3Pair T L I 1) := fun h8 => by
      have hm := mMat G T L I hyp hV hN hNM hc h8
      rw [nMat G T L I hyp hV hN hNM hc h8]
      exact ⟨by omega, Or.inl (by omega)⟩
    rcases hrow with h | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | ⟨n, h⟩ | h |
      h | h | ⟨n, h⟩
    · exact absurd h hU
    · obtain ⟨hm, hn3⟩ := mSz G T L I hyp hV hN hNM hc n h
      rw [nSz G T L I hyp hV hN hNM hc n h]
      exact ⟨by omega, Or.inl (by omega)⟩
    · have hm := mL3 G T L I hyp hV hN hNM hc n h
      have hn1 := h.1
      rw [nL3 G T L I hyp hV hN hNM hc n h]
      exact ⟨by omega, Or.inl (by omega)⟩
    · exact hmat (Or.inl h)
    · exact hmat (Or.inr (Or.inl h))
    · exact hmat (Or.inr (Or.inr (Or.inl h)))
    · exact hmat (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact hmat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact hmat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact hmat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact hmat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
    · have hm := mSL3 G T L I hyp hV hN hNM hc n h
      rcases Nat.lt_or_ge n 2 with hn | hn
      · have h1 : n = 1 := le_antisymm (by omega) (one_le_of_row711SL3Pair h)
        subst h1
        rw [nSL1 G T L I hyp hV hN hNM hc h]
        exact ⟨by omega, Or.inr h⟩
      · rw [nSL3 G T L I hyp hV hN hNM hc n hn h]
        exact ⟨by omega, Or.inl (by omega)⟩
    · obtain ⟨htw, ⟨n, hn2, hs⟩ | ha⟩ := h
      · obtain ⟨hsp, -⟩ := hSp4 G T L I hyp hV hN hNM hc htw
        have hm := (hsp n hn2 hs).2
        rw [nSp4 G T L I hyp hV hN hNM hc htw n hn2 hs]
        exact ⟨by omega, Or.inl (by omega)⟩
      · obtain ⟨-, hA6⟩ := hSp4 G T L I hyp hV hN hNM hc htw
        have hm := (hA6 ha).2
        rw [nA6 G T L I hyp hV hN hNM hc htw ha]
        exact ⟨by omega, Or.inl (by omega)⟩
    · obtain ⟨-, hm, -⟩ := hS7 G T L I hV hN hNM hc h
      rw [nS7 G T L I hyp hV hN hNM hc h]
      exact ⟨by omega, Or.inl (by omega)⟩
    · have hm := mWr G T L I hyp hV hN hNM hc h
      rw [nWr G T L I hyp hV hN hNM hc h]
      exact ⟨by omega, Or.inl (by omega)⟩
    · exact absurd h (h731 hc n)
  have hr : (nPrime (autI hV ⊤) : ℕ∞) < rParam (fsuV T I) := by
    by_cases hU : Row711SU3 T L I
    ·
      obtain ⟨n, hn2, h⟩ := hU
      obtain ⟨-, -, -, hβ, hα⟩ := stmt7_2_1_SU3 G T L I hyp hV hNM hc n hn2 h
      have hTL := h711n G T L I hyp hc (Or.inl ⟨n, hn2, h⟩)
      have hβr := betaH_le_rParam_of_alpha hin h325 hyp h731 hTL hV hN hNM hα
      rw [nSU3 G T L I hyp hV hN hNM hc n hn2 h]
      have h24 : ((2 * n : ℕ) : ℕ∞) < ((4 * n : ℕ) : ℕ∞) := by exact_mod_cast (by omega)
      exact lt_of_lt_of_le h24 (hβ.trans hβr)
    · rcases (hnm hU).2 with hm2 | h1
      · exact lt_of_lt_of_le (by exact_mod_cast (hnm hU).1)
          (mParam_le_rParam_of_ti h37 h38 h39 hmod h3228 h63 hyp hstr.1 hV hm2)
      · have h2 := h771 G T L I hyp h731 hc h1
        rw [nSL1 G T L I hyp hV hN hNM hc h1]
        exact lt_trans (by norm_num) h2
  obtain ⟨hall, hw⟩ := wParam_le_nPrime_of_e22 hE22 h331 hyp hV hE336
    ((Subgroup.centralizer_le_normalizer _).trans hNM) hr
  exact ⟨hall, hw, ⟨fun _ hU => nPrime_lt_sParam hV hr (hnm hU).1, fun _ _ => hr⟩, hk⟩

end CFSG.Quasithin.H13
