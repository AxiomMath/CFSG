module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN3e
public import CFSG.Quasithin.H13.GoldschmidtM22EndN2

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

theorem endN3 (hG : G64Out) (h621 : Stmt6_2_1) (h622 : Stmt6_2_2)
    (h626 : Stmt6_2_6) (h629 : Stmt6_2_9) (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11)
    (h6212 : Stmt6_2_12) (h : Hyp6Sec2 G T M L V) (hZS : ch6ZS T L V = V ⊓ UU T L V) :
    ∃ (g : G) (D : Subgroup G), KData T L V g D := by
  obtain ⟨P⟩ := endN2 hG h621 h622 h626 h629 h6210 h6211 h6212 h hZS
  exact P.kData h (h622 G T M L V h).2.1 h621 h626 h6210 h6211 h6212

end CFSG.Quasithin.H13.GM22
