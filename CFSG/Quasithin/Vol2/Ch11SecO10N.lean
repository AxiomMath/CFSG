module

public import CFSG.Quasithin.Vol2.Ch11SecO10H
public import CFSG.Quasithin.Vol2.Ch11SecO10I
public import CFSG.Quasithin.Vol2.Ch11SecO10M
public import CFSG.Quasithin.Vol2.Ch11SecE42S3Obl
public import CFSG.Quasithin.Vol2.Ch11SecO10G

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 SecE

theorem obl11_4_2S3Lie_of (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43) (hF44 : Facts44)
    (hF15 : SecA.Facts15) (hP : SecB.PointFacts) (hN : SecA.NatFacts) (hPar : ParInFacts)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (hFSU : Ch10.StmtFSUChoice)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1104 : Stmt11_0_4)
    (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1115 : Stmt11_1_5) (h1132 : Stmt11_3_2)
    (h1141 : Stmt11_4_1) : Obl11_4_2S3Lie := by
  intro G _ _ T L I n V₁ z hc hmax _ hK
  obtain ⟨I', hK'⟩ := exists_hyp11_kz hF hS hF43 hP h1102 h1110 h1111 h1141 h37 h39 hFSU hc hmax hK
  have h := hc.hyp
  obtain ⟨-, hLK, -, -, -, -⟩ := conf_spec hF43 h1102 h1110 h1111 h1141 hc
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hcV := (h1141 G T L I n V₁ X h hc.vi hX).1.1
  have hKN := (kz_spec hF43 h1102 h1110 h1111 h hcV hc.vi hc.mem hc.ne_one).2.1
  obtain ⟨V'₁, hV'₁, -⟩ := (h1110 G T _ I' n hK').1 1 le_rfl (by norm_num)
  obtain ⟨V'₂, hV'₂, -⟩ := (h1110 G T _ I' n hK').1 2 (by norm_num) (by norm_num)
  obtain ⟨V'₃, hV'₃, -⟩ := (h1110 G T _ I' n hK').1 3 (by norm_num) le_rfl
  have hk : KindSL3 (kz L V₁ z) (fsuV T I') n ∨ KindSp4 (kz L V₁ z) (fsuV T I') n := by
    rcases SecA.kind_cases h1102 hK' with hk | hk | hk
    · exact Or.inl hk
    · exact Or.inr hk
    · exact (not_kindG2_kz h331 h1132 hK' hV'₁ (mem_omegaOneCenter_of h hc.mem) hKN hk).elim
  have hSK := SecD.natSetting11_of h1102 h1141 hK' hV'₁
  rcases lOf_le_normalizer_or h1110 h hc.vi hSK hk hK' hV'₁ hV'₂ hV'₃ hLK with h1 | h2
  · exact false_of_rOf_eq_rOf_one hF hF43 hN hPar h1102 h1110 h1111 h1115 h1141 hc hK' hV'₁
      (rOf_eq_of_le_normalizer h1110 h hc.vi hK' (Or.inl rfl) hV'₁ hLK h1)
  · exact false_of_rOf_eq_rOf_two hF43 hF44 hF15 hN h331 h1102 h1103 h1104 h1110 h1111 h1115
      h1141 hc hK' hk hV'₁ hV'₂
      (le_perfectCore_of_perfect (le_inf hLK h2) (perfectCore_perfect _))
      (rOf_eq_of_le_normalizer h1110 h hc.vi hK' (Or.inr rfl) hV'₂ hLK h2)

end CFSG.Quasithin.Vol2.Ch11.O10
