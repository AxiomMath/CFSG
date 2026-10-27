module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Sec8Hyp.large (h54 : Stroth54Statement) (hge : Stroth6NbarGeStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (h : Sec8Hyp hc n t) :
    Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN t) := by
  have h1 := hge G M Q Z B hc n h.toSec5.width h.toSec5.n_gt h.toSec5.noA2 h.toSec5.gen t
    h.toSec5.mem h.toSec5.notQ
  have h2 := h54 G M Q Z B hc n t h.toSec5 h.spNat
  exact lt_of_le_of_ne h1 (Ne.symm h2)

theorem stroth81_of_steps (hV : Step81VanishStatement) (hT : Step81TypeStatement)
    (hC : Step81CloseStatement) : Stroth81Statement := by
  intro G _ _ M Q Z B hc n t hs r hr
  by_cases ha : Conc81a hc t
  · exact Or.inl ha
  · refine Or.inr ?_
    have hv := hV G M Q Z B hc n t hs r hr ha
    by_cases hex : ∃ x : G, ConjMod M Q t x ∧ ⁅x, t⁆ ∈ Q ∧
        ∃ w ∈ Sec8W1 M Q Z B t r, ⁅x, w⁆ ∉ Sec8V1 M Q Z B t r
    · exact ⟨hT G M Q Z B hc n t hs r hr ha hex, hex, hv⟩
    · exfalso
      refine hC G M Q Z B hc n t r ⟨hs, hr, ha, fun x hx hxt w hw => ?_⟩
      by_contra hn
      exact hex ⟨x, hx, hxt, w, hw, hn⟩

theorem step81close_of_parts (hE : Close81EStatement) (hS : Close81SylowStatement)
    (hTI : Sec8TIStatement) (hF : Close8FinalStatement) : Step81CloseStatement := by
  intro G _ _ M Q Z B hc n t r h
  have h' := h
  obtain ⟨hs, hr, ha, hx⟩ := h'
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre hs.toSec5.mem
  haveI := hc.normal_Q_in_M
  exact hF G M Q Z B hc n t hs ha Z0 hZ0 (hTI G M Q Z B hc n t hs Z0 hZ0)
    (hS G M Q Z B hc n t r h Z0 hZ0) (hE G M Q Z B hc n t r h Z0 hZ0)

end CFSG.RankThree.GF2n.Stroth80
