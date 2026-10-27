module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93XH
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TF
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93NDich

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conjB_le_QB_of_L2 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hX : Classify.TheoremXStatement) {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G}
    {h : G} (cfg : Cfg93c hc n t r Z0 h)
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z))) :
    conjSubgroup h B ≤ QB B := by
  classical
  have hQK : Q ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B) :=
    le_inf sec39_Q_le_LB (by
      calc Q = conjSubgroup h Q := (hc.conj_Q_eq cfg.hh).symm
        _ ≤ conjSubgroup h (LB M Q B) := Subgroup.map_mono sec39_Q_le_LB)
  have hlt : Q < LB M Q B ⊓ conjSubgroup h (LB M Q B) := lt_of_le_of_ne hQK (Ne.symm cfg.hK)
  obtain ⟨x, hxK, hxQ⟩ := Set.exists_of_ssubset hlt
  have hxL : x ∈ LB M Q B := (Subgroup.mem_inf.mp hxK).1
  have hxLh : x ∈ conjSubgroup h (LB M Q B) := (Subgroup.mem_inf.mp hxK).2
  have hs : Sec5Hyp hc n x := ⟨cfg.hs.toSec5.width, cfg.hs.toSec5.n_gt, cfg.hs.toSec5.noA2,
    cfg.hs.toSec5.gen, hxL, hxQ⟩
  by_cases hSL : SLNat hc x
  · exact (sec39_conjB_le_Vt cfg.hh hxLh).trans (stroth310SL_of_34 h34 G M Q Z B hc n x hs hSL)
  rcases conj_le_QB_or_eq_Rt h34 hX h311a hs hSL (m₁ := 1) (m₂ := h) M.one_mem cfg.hh
    (by rw [conjSubgroup_one]; exact hxL) hxLh (by rw [conjSubgroup_one]; exact cfg.hne) with
    h1 | ⟨hR, hcount⟩
  · rwa [conjSubgroup_one] at h1
  · exfalso
    rw [conjSubgroup_one] at hR hcount
    have hF₀ : Fhat M Q B h = Nt M (LB M Q B) x := by
      show inSubgroup (pCore 2) (Xhat M Q B h) = inSubgroup (pCore 2) (Rt M (LB M Q B) x)
      rw [show Xhat M Q B h = Rt M (LB M Q B) x from hR]
    have hFN : Fhat M Q B h ≤ hc.CN x := hF₀ ▸ hc.Nt_le_CN h34 hs
    have hne : (Fhat M Q B h).relIndex (LB M Q B) ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 := Subgroup.relIndex_le_of_le_left hFN hne
    have h2 := relIndex_Fhat_le hc hq
    have h4 : 4 ≤ Nat.card Z := hc.hyp.q4
    nlinarith

end HS9

end CFSG.RankThree.GF2n.Stroth80
