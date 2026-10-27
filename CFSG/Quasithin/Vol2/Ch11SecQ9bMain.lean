module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bI2
public import CFSG.Quasithin.Vol2.KGNatSL3LineFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

theorem stmt11_1_2_of (hF : Facts12) (hFb : Facts12b) (hFc : Facts12c) (hC : CartanFacts)
    (hF11 : Facts11) (hN : NatFacts) (hLp : FactLineSp4) (hLg : FactLineG2)
    (hPG : SecS.FactParabGen) (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h133 : Tmp1_3_3)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1111 : Stmt11_1_1)
    (hStar : Stmt11_1_2Star) : Stmt11_1_2 := by
  intro G _ _ T L I n i Vi V₁ V₂ X h hi hVi hV₁ hV₂ hX
  rcases hi with rfl | rfl
  · obtain rfl : Vi = V₁ := IsVi.eq hN h1102 h le_rfl (by norm_num) hVi hV₁
    obtain ⟨K, hLK, hK, hNK, hcases⟩ := h1111 G T L I n 1 Vi Vi h hVi
      (Or.inl ⟨rfl, IsVi.ne_bot h hVi le_rfl, le_rfl,
        C11P9B.isSylowTwoOf_inf_normalizer_V1 h hVi⟩)
    refine ⟨K, hLK, hK, hNK, charTwo_of_cComp h hVi le_rfl hK hNK, ?_⟩
    rcases C11P9B.case_i1 hFb hC hF hF11 hN h318 h36 h38 h331 h1102 hStar h hVi hV₂ hX hK hNK
        hLK hcases with heq | ⟨hn, h3 | h2 | h1⟩
    · exact Or.inl heq
    · exact Or.inr ⟨rfl, hn, Or.inr (Or.inr h3.1)⟩
    · exact Or.inr ⟨rfl, hn, Or.inr (Or.inl h2.1)⟩
    · exact Or.inr ⟨rfl, hn, Or.inl h1.1⟩
  · obtain rfl : Vi = V₂ := IsVi.eq hN h1102 h (by norm_num) (by norm_num) hVi hV₂
    obtain ⟨K, hLK, hK, hNK, hcases⟩ := h1111 G T L I n 2 Vi Vi h hVi (Or.inr ⟨rfl, rfl⟩)
    exact ⟨K, hLK, hK, hNK, charTwo_of_cComp h hVi (by norm_num) hK hNK,
      Or.inl (C11P9B.case_i2 hF hFb hFc hC hF11 hN KGNat.factLineSL3_holds hLp hLg hPG h318 h36
        h38 h36c h133 h331 h1102 h1103 h1111 hStar h hV₁ hVi hX hK hNK hLK hcases)⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
