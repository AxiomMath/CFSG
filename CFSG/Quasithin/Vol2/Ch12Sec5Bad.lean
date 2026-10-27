module

public import CFSG.Quasithin.Vol2.Ch12Sec5L3Ex
public import CFSG.Quasithin.Vol2.Ch12Sec5Hat7
public import CFSG.Quasithin.Vol2.Ch12Sec5E49
public import CFSG.Quasithin.Vol2.Ch12Sec5Gam
public import CFSG.Quasithin.Vol2.Ch12Sec5KGL52
public import CFSG.Quasithin.Vol2.Ch12Sec5KGJ4Bar
public import CFSG.Quasithin.Vol2.Ch12Sec5Elim
public import CFSG.Quasithin.Vol2.KGFact1291S3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125

namespace S125Bad

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem centralizer_V6_le
    (hF : A318Facts) (hDyn : DynkinFact1293) (h1222 : Stmt12_2_2) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    Subgroup.centralizer (F.V6 : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨K₁, hLK, hK, hK₁n⟩ := S125K1.exists_k1 h1222 h37 h38 h39 F hH
  rcases eq_or_lt_of_le hLK with h | h
  · rw [← h] at hK₁n
    exact S125L4.centralizer_V6_le h1222 F hH hK₁n
  have hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G) := le_of_mem_cComp hK
  rcases S125K1.list_of h1222 h36 h312 hDyn F hH hK h hK₁n with hl | hl
  · have hPK := S125O2P.oTwoUpper_P_le_of_list2 hF h36 h38 h1222 F hH hK hl
    refine S125Cfg.centralizer_V6_le_of_alpha h1222 h36 h37 h38 h39 h312 F hH hK₁n hKG hLK hPK ?_
    rcases hl with h' | h' | h'
    · exact fun S N D hS hc => S125KG.L52.kg125AlphaL52 _ h' S N D hS hc
    · exact fun S N D hS hc => S125KG.M24.kg125AlphaM24 _ h' S N D hS hc
    · exact fun S N D hS hc => S125KG.J4.kg125AlphaJ4 _ h' S N D hS hc
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
    · exact S125E49.centralizer_V6_le_of_e49 h1222 h36 h37 h38 h39 h312 F hH hK hK₁n hLK h'

theorem lemma12_5_4six
    (hF : A318Facts) (hDyn : DynkinFact1293) (h1222 : Stmt12_2_2) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK) :
    Lemma12_5_4six :=
  fun _ _ _ _ _ _ F hH => S125L4.normalizer_V6_le h1222 h36 h37 h38 h39 h312 F hH
    (centralizer_V6_le hF hDyn h1222 h36 h37 h38 h39 h312 F hH)

theorem k1Bad125_of
    (hF : A318Facts) (hDyn : DynkinFact1293) (h1222 : Stmt12_2_2) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) (h312 : A312ForSQTK) (h1228 : Stmt12_2_8) (h6 : Lemma12_5_6)
    (h7 : Lemma12_5_7) (h10 : Lemma12_5_10) : K1Bad125 := by
  intro G _ _ T L V F K₁ hH hK hLK hK₁n
  have hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G) := le_of_mem_cComp hK
  have hf := S125Ex.Facts125.of h1222 hH
  have hTG₁ : T ≤ Subgroup.normalizer (F.V1 : Set G) := (S125L2G.T_le_V F hf.T_le).1
  obtain ⟨H, hTH, hHK, hs, hHM⟩ : ∃ H : Subgroup G, T ≤ H ∧ H ≤ K₁ ⊔ T ∧
      Group.IsSolvable ↥H ∧ ¬ H ≤ Subgroup.normalizer (L : Set G) := by
    rcases S125K1.list_of h1222 h36 h312 hDyn F hH hK hLK hK₁n with hl | hl
    · exact S125Gam.exists_solvable_of_list2 S125KG.M24.kg125GammaM24 S125KG.J4.kg125GammaJ4
        s3OvergroupFact_holds h1228 h1222 F hH hK hLK hK₁n hl
    · rcases hl with h' | h' | h' | h' | h' | h' | h' | h'
      · exact (S125L3.false_of_list3 hF h36 h38 h1222 F hH hK hK₁n hLK.le (Or.inl h')).elim
      · exact (S125L3.false_of_list3 hF h36 h38 h1222 F hH hK hK₁n hLK.le
          (Or.inr (Or.inl h'))).elim
      · exact (S125Hat7.false_of_hat7 hF h36 h38 h1222 F hH hK hK₁n hLK.le h').elim
      · exact (S125L3.false_of_list3 hF h36 h38 h1222 F hH hK hK₁n hLK.le
          (Or.inr (Or.inr (Or.inl h')))).elim
      · exact (S125L3.false_of_list3 hF h36 h38 h1222 F hH hK hK₁n hLK.le
          (Or.inr (Or.inr (Or.inr (Or.inl h'))))).elim
      · exact (S125L3.false_of_list3 hF h36 h38 h1222 F hH hK hK₁n hLK.le
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))).elim
      · exact (S125L3.false_of_list3 hF h36 h38 h1222 F hH hK hK₁n hLK.le
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h')))))).elim
      · exact S125E49.exists_solvable_of_e49 h1222 F hH hK hK₁n hLK.le h'
  exact S125Gam.false_of_solvable h6 h7 h10 hH F hTH (hHK.trans (sup_le hKG hTG₁)) hs hHM

end S125Bad

end CFSG.Quasithin.H13
