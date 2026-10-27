module

public import CFSG.Quasithin.Vol2.Ch11SecG556Choice
public import CFSG.Quasithin.Vol2.Ch11SecG556Transv

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.CosetGeom

theorem stmt11_5_8_of (hTrans : FactTransv11_5_8)
    (hShape : FactCase1Shape) (hAct : SecD.FactCase1PrimeAct) (hCE : CommEndStableFact)
    (hR1 : R1CommFact) (hPt : PointConjFact) (hCor : R1CorankFact) (hTI : SecD.PointsTIFact)
    (hCard : SecD.CardVFact) (h331 : Stmt3_3_1) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1112 : Stmt11_1_2)
    (h1122 : Stmt11_2_2) (h1141 : Stmt11_4_1) (h1142 : Stmt11_4_2) (h1143 : Stmt11_4_3)
    (h1151 : Stmt11_5_1) (h1155 : Stmt11_5_5) (h1156 : Stmt11_5_6) (h1157 : Stmt11_5_7) :
    Stmt11_5_8 := by
  intro G _ _ T L I n V₁ h hV₁
  by_contra hne
  obtain ⟨H₁, hc, hHM, hcase⟩ :=
    exists_h1Choice hShape hTI h1102 h1110 h1111 h1112 h1141 h1143 h hV₁ hne
  have hinH := hc.inH h hV₁
  have hHN := hc.le_normalizer hV₁
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hsix := (h1156 G T L I n V₁ X H₁ h hV₁ hX hinH hHM hHN).2.2.2.2.2.2
    (hc.oTwoUpper_le h hV₁) hcase
  obtain ⟨V₃, hV₃, -⟩ := (h1110 G T L I n h).1 3 (by norm_num) (by norm_num)
  rcases Nat.even_or_odd (critDist (L ⊔ T ⊔ H₁) (L ⊔ T) H₁ (fsuV T I)) with hb | hb
  · exact false_of_even h1102 h1110 h1141 h1151 h1157 hCE hR1 hPt h hV₁
      (amalgamHypV_of_inH h331 h3228 h hinH hHM) (pCoreOf_inf_le_ROf_of_le h hc.lT_le) hb
  · rcases hc with rfl | ⟨p, hp, hp5, hK1, hPM, rfl⟩
    · exact false_of_odd hCor h331 h3228 h1102 h1110 h1122 h1141 h1151 h1155 h1157 h hV₁ hV₃
        hinH hHM hHN hsix
        (fun _ hgO hU => inf_conjSub_eq_bot hTI hPt h331 h1102 h1141 h1142 h1151 h hV₁ hgO hU)
        (fun _ hAH hA2 hAO hAY => false_of_transv_kt hTrans hCard hTI h331 h1102 h1110 h1111
          h1112 h1122 h1141 h1143 h1151 h1157 h hV₁ hV₃ hne hAH hA2 hAO hAY) hb
    · have hPQ : ¬ oTwoPrime (KOf L V₁ V₁) p ≤ pCoreOf 2 (KOf L V₁ V₁) := fun hle =>
        hPM (hle.trans ((pCoreOf_kOf_le_T h hV₁).trans h.normal))
      have hF2 := (primeAct_of hAct h1110 h1111 h hV₁ hne hp hK1 hPQ).1
      exact false_of_odd hCor h331 h3228 h1102 h1110 h1122 h1141 h1151 h1155 h1157 h hV₁ hV₃
        hinH hHM hHN hsix
        (fun _ hgO hU => inf_conjSub_eq_bot_prime hTI hPt h331 h1102 h1141 h1142 h1151 h1157 h
          hV₁ hp (by omega) hF2 hgO hU)
        (fun _ hAH hA2 hAO hAY => false_of_transv_prime hAct hCard h331 h1102 h1110 h1111 h1112
          h1122 h1141 h1151 h1157 h hV₁ hV₃ hne hp hp5 hK1 hPQ hAH hA2 hAO hAY) hb

end CFSG.Quasithin.Vol2.Ch11.SecG
