module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93OmB
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93SLCase
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TMain

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank


@[expose] def Step93OmegaCaseBNSStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
    (t r : G) (Z0 : Subgroup G) (h : G), HS9.Cfg93c hc n t r Z0 h →
    ∀ x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B), x ∉ Q → ¬ SLNat hc x →
      LB M Q B ⊔ conjSubgroup h (LB M Q B) = Rt M (LB M Q B) x →
      ¬ LB M Q B ⊓ hc.CN t ≤
        inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)) → False

theorem step93OmegaCaseB_of_NS (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h312b : Stroth312bStatement) (hNS : Step93OmegaCaseBNSStatement)
    (hAlt : Step93L2AltXHStatement) : Step93OmegaCaseBStatement := by
  intro G _ _ M Q Z B hc n t r Z0 h cfg x hxK hxQ hR hLN
  by_cases hSL : SLNat hc x
  · have hxL : x ∈ LB M Q B := (Subgroup.mem_inf.mp hxK).1
    have hxLh : x ∈ conjSubgroup h (LB M Q B) := (Subgroup.mem_inf.mp hxK).2
    have hq := HS9.slPair_quotSat h34 h311a G M Q Z B hc n cfg.hs.toSec5.width
      cfg.hs.toSec5.n_gt cfg.hs.toSec5.noA2 cfg.hs.toSec5.gen x hxL hxQ (LB M Q B)
      (conjSubgroup h (LB M Q B)) ⟨1, Subgroup.one_mem M, (conjSubgroup_one (LB M Q B)).symm⟩
      ⟨h, cfg.hh, rfl⟩ hxL hxLh cfg.hne hSL
    rcases hAlt G M Q Z B hc n t r Z0 h cfg hq with h1 | h2
    · exact step93L2_false_of_le_H hc cfg.hs cfg.hZ0
        (step93L2First_of h34 h311a h311bComm h311bCard h312b G M Q Z B hc n t r Z0 h cfg hq h1)
        cfg.hZQ
    · exact step93L2Second_of h34 h311a h311bComm h311bCard G M Q Z B hc n t r Z0 h cfg hq h2
  · exact hNS G M Q Z B hc n t r Z0 h cfg x hxK hxQ hSL hR hLN

end CFSG.RankThree.GF2n.Stroth80
