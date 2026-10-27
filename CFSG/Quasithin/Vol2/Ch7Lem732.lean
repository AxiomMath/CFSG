module

public import CFSG.Quasithin.Vol2.Ch7Lem734Main
public import CFSG.Quasithin.Vol2.Ch3Sec2Wreath

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem row711SL3Pair_one_of_mParam_le_two (hSp4 : Stmt7_2_1_Sp4Pair) (hS7 : Stmt7_2_1_S7)
    (mSz : Stmt7_2_1_m_Sz) (mL3 : Stmt7_2_1_m_L3Nine) (mMat : Stmt7_2_1_m_Mathieu)
    (mSL3 : Stmt7_2_1_m_SL3Pair) (mWr : Stmt7_2_1_m_L3Wreath) (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) [hc : IsMulCommutative ↥(fsuV T I)]
    (hrow : Rows7_1_1 T L I) (hm : mParam (autI hV ⊤) ≤ 2) : Row711SL3Pair T L I 1 := by
  have hmat : ¬ (Row711M12 T L I ∨ Row711M22Hat T L I ∨ Row711M22Code T L I ∨
      Row711M22Cocode T L I ∨ Row711M23Code T L I ∨ Row711M23Cocode T L I ∨
      Row711M24Code T L I ∨ Row711M24Cocode T L I) := fun h8 => by
    have := mMat G T L I hyp hV hN hNM hc h8
    omega
  rcases hrow with ⟨n, hn2, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | ⟨n, h⟩ | h |
    h | h | ⟨n, h⟩
  · have := (stmt7_2_1_SU3 G T L I hyp hV hNM hc n hn2 h).2.1
    omega
  · obtain ⟨h2n, hn3⟩ := mSz G T L I hyp hV hN hNM hc n h
    omega
  · have h3n := mL3 G T L I hyp hV hN hNM hc n h
    have hn1 := h.1
    omega
  · exact (hmat (Or.inl h)).elim
  · exact (hmat (Or.inr (Or.inl h))).elim
  · exact (hmat (Or.inr (Or.inr (Or.inl h)))).elim
  · exact (hmat (Or.inr (Or.inr (Or.inr (Or.inl h))))).elim
  · exact (hmat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).elim
  · exact (hmat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).elim
  · exact (hmat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))).elim
  · exact (hmat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))).elim
  · have h2n := mSL3 G T L I hyp hV hN hNM hc n h
    obtain rfl : n = 1 := le_antisymm (by omega) (one_le_of_row711SL3Pair h)
    exact h
  · obtain ⟨htw, ⟨n, hn2, hs⟩ | ha⟩ := h
    · have := ((hSp4 G T L I hyp hV hN hNM hc htw).1 n hn2 hs).2
      omega
    · have := ((hSp4 G T L I hyp hV hN hNM hc htw).2 ha).2
      omega
  · have := (hS7 G T L I hV hN hNM hc h).2.1
    omega
  · have := mWr G T L I hyp hV hN hNM hc h
    omega
  · exact absurd h (h731 hc n)

theorem stmt7_3_2_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h63 : ASInputs.AS_E_6_3) (h711 : Stmt7_1_1)
    (h711n : Stmt7_1_1_normal) (h771 : Stmt7_7_1) (hSp4 : Stmt7_2_1_Sp4Pair)
    (hS7 : Stmt7_2_1_S7) (mSz : Stmt7_2_1_m_Sz) (mL3 : Stmt7_2_1_m_L3Nine)
    (mMat : Stmt7_2_1_m_Mathieu) (mSL3 : Stmt7_2_1_m_SL3Pair) (mWr : Stmt7_2_1_m_L3Wreath) :
    Stmt7_3_2 := by
  intro G _ _ T L I hyp h731 hV
  have hmod := stmtFSUModule_of_eight h3228
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  obtain ⟨hc, hrow⟩ := h711 G T L I hyp
  by_cases hm : 2 < mParam (autI hV ⊤)
  ·
    have hTI : IsTISetUnder (fsuV T I) (fsuM T L) := by
      by_cases hTL : T ≤ Subgroup.normalizer (L : Set G)
      · exact isTISetUnder_of_le_normalizer h325 hyp.fsu hTL
      · rcases rows_cases hrow with h | h | ⟨n, h⟩
        · exact absurd (h711n G T L I hyp hc h) hTL
        · exact (isTISetUnder_fsuV_of_row711L3Wreath hyp.fsu h).2
        · exact absurd h (h731 hc n)
    exact mParam_le_rParam_of_ti h37 h38 h39 hmod h3228 h63 hyp hTI hV hm
  ·
    have h1 := row711SL3Pair_one_of_mParam_le_two hSp4 hS7 mSz mL3 mMat mSL3 mWr hyp h731 hV hN
      hNM hrow (by omega)
    have hm2 : (mParam (autI hV ⊤) : ℕ∞) ≤ 2 := by exact_mod_cast (not_lt.mp hm)
    exact hm2.trans (h771 G T L I hyp h731 hc h1).le

end CFSG.Quasithin.H13
