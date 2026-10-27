module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFStmt
public import CFSG.Quasithin.Vol2.Ch3Sec3NFFacts

public section

namespace CFSG.Quasithin.H13.L3314

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)

theorem obl3_3_13D12NFOn_314line_of (h36 : A36ForSQTK)
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Obl3_3_13D12NFOn Site3314line := by
  intro G _ _ T M L D H K h hP hH hHLT hwr hO hK hKq hYK hTK hKf _ hq
  obtain ⟨-, hline⟩ := hP
  have c : NFConfig G T M L D H K := ⟨h, hH, hHLT, hwr, hO, hK, hKq, hYK, hTK, hKf, hq⟩
  have hYC : oTwoUpper H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    hYK.trans (nf_conjClosure_le_centralizer_Z h36 h c.inH_H₀ hK hKf)
  have hC0 := c.inf_centralizer_mPlus_eq_bot h36 h5 h128 h37 h38 h39
  have h74 : vPlus L T = ⁅vPlus L T, mPlus L T⁆ := by
    have := (h7 G T M L D h).2.2.2.2
    rwa [hC0, sup_bot_eq] at this
  have hZV : quasithinOmegaOneCenter T ≤ vPlus L T := le_conjClosure _ _
  have hZ : quasithinOmegaOneCenter T ≤
      ⁅vPlus L T, mPlus L T⁆ ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := fun z hz =>
    ⟨h74 ▸ hZV hz, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hYC hy) z hz).symm⟩
  rw [hline, le_bot_iff] at hZ
  exact quasithinOmegaOneCenter_ne_bot h.sylow.1 h.toSetup331.T_ne_bot hZ

theorem obl3_3_13D12NF_314_of (h36 : A36ForSQTK)
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hpt : Obl3_3_13D12NF_314pt) :
    Obl3_3_13D12NF_314 := by
  intro G _ _ T M L D H K h hP hH hHLT hwr hO hK hKq hYK hTK hKf hin hq
  by_cases hline : ⁅vPlus L T, mPlus L T⁆ ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥
  · exact obl3_3_13D12NFOn_314line_of h36 h5 h7 h128 h37 h38 h39 G T M L D H K h ⟨hP, hline⟩ hH
      hHLT hwr hO hK hKq hYK hTK hKf hin hq
  · exact hpt G T M L D H K h ⟨hP, hline⟩ hH hHLT hwr hO hK hKq hYK hTK hKf hin hq

end CFSG.Quasithin.H13.L3314
