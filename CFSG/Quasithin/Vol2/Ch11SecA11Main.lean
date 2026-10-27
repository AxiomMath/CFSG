module

public import CFSG.Quasithin.Vol2.Ch11SecA11Nonquasi2
public import CFSG.Quasithin.Vol2.Ch11SecA11Transport
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases2
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem stmt11_1_1_of
    (hF : Facts11) (hN : NatFacts) (h1102 : Stmt11_0_2) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK) :
    Stmt11_1_1 := by
  intro G _ _ T L I n i Vi V₀ h hU hc'
  have hc : Hyp1111 T i Vi V₀ := hc'
  obtain ⟨K, hK, hBK, hHK, hcases⟩ := exists_cComp_1111 hF hN h1102 h37 h38 h39 h312 h hU hc
  refine ⟨K, hBK, hK, hHK, ?_⟩
  have hD := barData_lOf hF hN h1102 h hU hc
  obtain ⟨e⟩ := modO2_mulEquiv hK
  rcases hcases with heq | hcase | hnq
  · exact Or.inl heq
  · exact Or.inr (Concl1111.of_mulEquiv e.symm (concl_of_a312Case hF.parab hD hcase))
  · have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot h.fsu.qtke h.fsu.simple h.fsu.nonabelian
      (hc.pCoreOf_ne_bot h hU)
    have h36s := h36 _ hQ _ (modO2Image_mem_cComp hK)
    have hBL : modO2Image (Subgroup.normalizer (V₀ : Set G)) (LOf L Vi) ≤
        modO2Image (Subgroup.normalizer (V₀ : Set G)) K :=
      Subgroup.map_mono fun x hx => hBK hx
    exact Or.inr (Concl1111.of_mulEquiv e.symm (concl_of_nonquasi hD hBL h36s hnq))

end CFSG.Quasithin.Vol2.Ch11.SecA
