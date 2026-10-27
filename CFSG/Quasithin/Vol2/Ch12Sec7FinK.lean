module

public import CFSG.Quasithin.Vol2.Ch12Sec7FinL34
public import CFSG.Quasithin.Vol2.Ch12Sec7FinJ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem final1271Para_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h2 : Lemma12_7_2) (h10 : Lemma12_7_10) (h11 : Lemma12_7_11) (h22 : Lemma12_7_22)
    (hL34 : Final1271L34Data) : Final1271Para := by
  intro G _ _ T L V t z hS H hHs hHz _ hpsl hL1T hr
  rcases hpsl with hpsl | hpsl
  · exact S127.false_of_l24 h331 h1222 h2 h10 h11 h22 hS hHs hpsl hL1T hr
  · obtain ⟨g, hgT, hgO⟩ := S127.exists_conj_not_le h11 hS hHs
    obtain ⟨g', H₁, hH₁H, hAT, hAH₁, hT₁, hτ, hpsl₁, hAO⟩ :=
      hL34 G T L V t z hS H hHs hHz hpsl hL1T g hgT hgO
    exact S127.false_of_h1Data h331 h1222 h2 h10 h22 hS hHs hL1T hr hH₁H hAT hAH₁ hT₁ hτ hpsl₁
      hAO

end CFSG.Quasithin.H13
