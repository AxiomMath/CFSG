module

public import CFSG.Quasithin.Background.F918Z6Main
public import CFSG.Quasithin.Background.F918Z1Main
public import CFSG.Quasithin.Background.F918Z7Syl
public import CFSG.Quasithin.Background.F918Z7aCaseI
public import CFSG.Quasithin.Background.F918Z7b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge

theorem z1Stmt_proved : Z1Stmt := by
  intro V _ _ hexp D X hcomm hV hirr hDnt hXnt
  exact fixV_eq_bot_of_irrPlus hexp hcomm hV hirr hDnt hXnt

theorem z37Main_proved
    (h45 : AsB45) (hF : Vol2.Ch10.SecA.Facts10_1) (hX : Insp5aNonShape) : Z37Main := by
  intro V _ _ D X G T' s hZ
  obtain ⟨A, hA, hAT⟩ := exists_qhatStar_le_sylow hZ.T_sylow hZ.qhat
  by_cases h : ∃ t ∈ A, ¬ D.map (MulAut.conj t).toMonoidHom = D
  · obtain ⟨t, htA, htD⟩ := h
    exact caseI_concl hZ hA hAT htA htD
  · push Not at h
    exact caseII_concl h45 hF hX hZ hA hAT h

theorem d37_proved
    (hL38 : D3L38) (hA21 : AsA21SQTKSection) (h45 : AsB45) (hF : Vol2.Ch10.SecA.Facts10_1)
    (hX : Insp5aNonShape) : D37 :=
  d37_of_z37 hL38 hA21 z1Stmt_proved (z37Main_proved h45 hF hX)

end CFSG.Quasithin
