module

public import CFSG.Quasithin.Vol2.Ch12Sec5Bad
public import CFSG.Quasithin.Vol2.Ch12Sec5BetaJ4
public import CFSG.Quasithin.Vol2.Ch12Sec5KGJ4Beta
public import CFSG.Quasithin.Vol2.Ch12Sec2StatementsPrime

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125

namespace S125Bad

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem V_le_pCoreOf_G1
    (hF : A318Facts) (hDyn : DynkinFact1293) (h1222 : Stmt12_2_2) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    V ≤ pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) := by
  obtain ⟨K₁, hLK, hK, hK₁n⟩ := S125K1.exists_k1 h1222 h37 h38 h39 F hH
  rcases eq_or_lt_of_le hLK with h | h
  · rw [← h] at hK₁n
    exact S125L8.V_le_pCoreOf h1222 F hH hK₁n
  rcases S125K1.list_of h1222 h36 h312 hDyn F hH hK h hK₁n with hl | hl
  · have hPK := S125O2P.oTwoUpper_P_le_of_list2 hF h36 h38 h1222 F hH hK hl
    rcases hl with h' | h' | h' <;> obtain ⟨e⟩ := h'
    · exact S125Beta.V_le_pCoreOf_of_beta S125KG.L52.kg125BetaL52 h1222 F hH hK hK₁n hLK hPK e
    · exact S125Beta.V_le_pCoreOf_of_beta S125KG.M24.kg125BetaM24 h1222 F hH hK hK₁n hLK hPK e
    · exact S125BetaJ4.V_le_pCoreOf_of_j4 S125KG.J4.kg125BetaJ4 CFSG.Sporadic.J4.isSimpleGroup_J4
        h1222 F hH hK hK₁n hLK hPK e
  · rcases hl with h' | h' | h' | h' | h' | h' | h' | h'
    · exact (S125L3.false_of_list3 hF h36 h38 h1222 F hH hK hK₁n hLK (Or.inl h')).elim
    · exact (S125L3.false_of_list3 hF h36 h38 h1222 F hH hK hK₁n hLK
        (Or.inr (Or.inl h'))).elim
    · exact (S125Hat7.false_of_hat7 hF h36 h38 h1222 F hH hK hK₁n hLK h').elim
    · exact (S125L3.false_of_list3 hF h36 h38 h1222 F hH hK hK₁n hLK
        (Or.inr (Or.inr (Or.inl h')))).elim
    · exact (S125L3.false_of_list3 hF h36 h38 h1222 F hH hK hK₁n hLK
        (Or.inr (Or.inr (Or.inr (Or.inl h'))))).elim
    · exact (S125L3.false_of_list3 hF h36 h38 h1222 F hH hK hK₁n hLK
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))).elim
    · exact (S125L3.false_of_list3 hF h36 h38 h1222 F hH hK hK₁n hLK
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h')))))).elim
    · exact S125E49.V_le_pCoreOf_of_e49 h1222 F hH hK hK₁n hLK h'

theorem lemma12_5_8
    (hF : A318Facts) (hDyn : DynkinFact1293) (h1222 : Stmt12_2_2) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (h7 : Lemma12_5_7) : Lemma12_5_8 := fun G _ _ T L V F hH =>
  have hV := V_le_pCoreOf_G1 hF hDyn h1222 h36 h37 h38 h39 h312 F hH
  ⟨hV, S125L8.isElemAbelian_u128 h1222 F hH (h7 G T L V hH) hV⟩

theorem elim125
    (hF : A318Facts) (hDyn : DynkinFact1293)
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (hpre : Pre1242)
    (h3228 : Stmt3_2_2_eight) (h1228 : Stmt12_2_8) (h1229 : Stmt12_2_9) (h12210 : Stmt12_2_10)
    (h2211 : Stmt12_2_11') (h1241 : Lemma12_4_1) (h42 : AsB42) (hE63 : ASInputs.AS_E_6_3)
    (hE612 : ASInputs.AS_E_6_12) (hE22 : E2.E22StatementC) (hTor : E2.E22TorusCover)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) : Elim125 := by
  have h4 := lemma12_5_4six hF hDyn h1222 h36 h37 h38 h39 h312
  have h6 := lemma12_5_6_of h331 h1222 h323 h3228 h12210 hE63 hE612 h4
  have h7 := lemma12_5_7_of h331 h1222 h323 h3228 h4 h6
  have h8 := lemma12_5_8 hF hDyn h1222 h36 h37 h38 h39 h312 h7
  have h9 := lemma12_5_9_of h331 h1222 h323 h3228 h12210 h7 h8
  have h10 := lemma12_5_10_of h331 h1222 h323 h3228 h4 h6 h7 h9
  exact elim125_of_k1 h331 h1222 h323 hpre h3228 h1228 h1229 h12210 h2211 h1241 h42 hE63 hE612
    hE22 hTor h36 h37 h38 h39 h312 (k1Bad125_of hF hDyn h1222 h36 h38 h312 h1228 h6 h7 h10)

end S125Bad

end CFSG.Quasithin.H13
