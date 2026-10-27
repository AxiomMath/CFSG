module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TB
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93XH
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreX
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TF

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem step93L2Second_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement) :
    Step93L2SecondStatement := by
  classical
  intro G _ _ M Q Z B hc n t r Z0 h cfg hq hH
  obtain ⟨hs, -, hZ0, hsc, hh, hne, -, -⟩ := cfg
  have hs5 := hs.toSec5
  have hn5 : 5 ≤ n := sec9NGeFive_of h34 h311a h311bComm h311bCard G M Q Z B hc n t hs
  have hCentre := step95Centre_of h34 h311a h311bComm h311bCard G M Q Z B hc n t hs Z0 hZ0
  have hZ0L : Z0 ≤ LB M Q B := (hCentre.1 : Z0 ≤ LB M Q B ⊓ hc.CN t).trans inf_le_left
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre hs5.mem hZ0
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hXH : HS9.Xhat M Q B h ≤ H0 M Z :=
    sup_le hc.LB_le_H0 (hLconj ▸ hc'.LB_le_H0)
  have hW : conjSubgroup h B ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
    by_cases hcase : Z0 ⊓ HS9.Fhat M Q B h ≤ Q
    · have hLF := HS9.inf_Fhat_le_conj_of_Z0 h34 hs5 hh hZ0L hQZ0 hCentre.2.1 hsc hcase hq
      obtain ⟨x, hx, hxQ⟩ := HS9.exists_mem_inf_CN_not_mem_Q h34 hs hn5
        (inf_le_left : LB M Q B ⊓ conjSubgroup h (LB M Q B) ≤ LB M Q B)
        (HS9.relIndex_Fhat_le hc hq) (by rw [inf_comm]; exact hLF) hH
      exact HS9.conjB_le_Wt_of_inf_CN h34 hs hh hx.1.1 hx.1.2 hx.2 hxQ
    · obtain ⟨s, hsmem, hsQ⟩ := SetLike.not_le_iff_exists.mp hcase
      have hFB' : ∀ f ∈ HS9.Fhat M Q B h, ∀ b ∈ conjSubgroup h B, ⁅f, b⁆ ∈ Z :=
        HS9.comm_mem_Z_of_pCoreIn h34 hc' hs5.width hs5.n_gt (hc.noA2_conj hs5.noA2 hh)
          (hs5.gen.conj_of_mem hh)
          (hLconj ▸ le_sup_right : LB M Q (conjSubgroup h B) ≤ HS9.Xhat M Q B h) hXH
      exact HS9.conjB_le_Wt_of_mem_F (hc := hc) (n := n) hc'.le hZ0L hCentre.2.2 hsmem.1 hsQ
        hsmem.2 hFB'
  exact HS9.false_of_conjB_le_Wt h34 hs hh hne hW hH

end CFSG.RankThree.GF2n.Stroth80
