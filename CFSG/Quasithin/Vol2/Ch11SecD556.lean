module

public import CFSG.Quasithin.Vol2.Ch11SecD556P
public import CFSG.Quasithin.Vol2.Ch11SecD556R
public import CFSG.Quasithin.Vol2.Ch11SecDGap556Three
public import CFSG.Quasithin.Vol2.Ch11SecD556C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem stmt11_5_6_of (hGap3 : Gap11_5_6Three) (hCart : CartanFact) (hM2 : FactM2Case1)
    (hM2P : FactM2Case1Prime) (hSig : L2pSignalizerFact) (hTI : PointsTIFact)
    (hF : SecA.NatFacts) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1)
    (h1112 : Stmt11_1_2) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1151 : Stmt11_5_1) :
    Stmt11_5_6 := by
  intro G _ _ T L I n V₁ X H₁ h hV₁ hX hH₁ hH₁M hH₁N
  have h3 := hGap3 G T L I n V₁ X H₁ h hV₁ hX hH₁ hH₁M hH₁N
  have h1 := stmt11_5_6_one hCart hF h1102 h1141 h1151 h hV₁ hX
  exact ⟨h1, stmt11_5_6_two h1110 h hV₁, fun hn => not_three_dvd_of_even h1 hn, h3,
    stmt11_5_6_four_of' hF h1102 h hV₁ hX h3,
    stmt11_5_6_five hTI h1102 h1110 h1112 h1141 h1143 h hV₁ hX,
    fun hOK hcase => stmt11_5_6_sixP hM2 hM2P hSig hTI h1102 h1110 h1111 h1112 h1141 h1143 h hV₁
      hX hH₁ hH₁M hH₁N hOK hcase⟩

end CFSG.Quasithin.Vol2.Ch11.SecD
