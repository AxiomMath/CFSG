module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreW
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreL
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CStmt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91Cent
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91QB

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem step95Centre_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement) :
    Step95CentreStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨r, hr⟩ := sec9AExists_of h34 h311a hNC G M Q Z B hc n t hs
  obtain ⟨hprod, hcomm, -⟩ := sec9_N51 h34 h311a hNC hs hr
  have heq := HS9.isCentrePre_eq_inf91 hs hr hprod hcomm hZ0
  have hZL : Z0 ≤ LB M Q B := by rw [heq]; exact inf_le_left
  have hZN : Z0 ≤ hc.CN t := HS9.isCentrePre_le_CN91 hs hZ0
  have hup := HS9.card_centrePre_le91 h34 h311bCard hs hZ0 hZL
  have hlow := HS9.centre95CardLower_holds91 h34 h311a h311bComm G M Q Z B hc n t hs Z0 hZ0
  have hcard : Nat.card Z0 = Nat.card Q * Nat.card Z := le_antisymm hup hlow
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  refine ⟨le_inf hZL hZN, ?_, fun s hsZ hsQ => ?_⟩
  · have h1 := Subgroup.relIndex_mul_card (H := Q) (K := Z0)
    rw [inf_of_le_left hQZ0, hcard] at h1
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hQpos (by rw [h1]; ring)
  · exact HS9.centre_clause91 h34 (stroth91b_of_steps h34 h311a hNC (step91OrderQB_of h34)
      (step91OrderVQB_of h34) (step91Inter_of h34) (step91MixedComm_of h34)) hs hr hZ0 hsZ hsQ

end CFSG.RankThree.GF2n.Stroth80
