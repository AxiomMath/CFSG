module

public import CFSG.RankThree.GF2n.Stroth80.Sec93OmegaIrred
public import CFSG.RankThree.GF2n.Stroth80.Sec93OmegaHolds
import CFSG.RankThree.GF2n.Stroth80.Sec84Holds
import CFSG.RankThree.GF2n.Stroth80.Sec7Stroth78Holds
import CFSG.RankThree.GF2n.Stroth80.Sec7Unconditional

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Certs


namespace S93O

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G} {h : G}

theorem omegaPlusFourNat_of_cfg (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxH : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hxQ : x ∉ Q) (hSL : ¬ SLNat hc x) :
    OmegaPlusFourNat hc x := by
  have hs5 : Sec5Hyp hc n x :=
    ⟨cfg.hs.toSec5.width, cfg.hs.toSec5.n_gt, cfg.hs.toSec5.noA2, cfg.hs.toSec5.gen,
      hxH.1, hxQ⟩
  have hR : Rt M (LB M Q B) x ≠ LB M Q B := Rt_ne_LB cfg hxH.2
  have h34 : Stroth34Statement := stroth34Statement_unconditional
  by_cases hV : Vt M (LB M Q B) B Z x ≤ QB B
  · exact (hSL (stroth310SLBranch_of_34 h34 G M Q Z B hc n x hs5 hR hV)).elim
  · have hCl : Stroth310ClassifyStatement :=
      stroth310Classify_of_mcLaughlin h34 mcLaughlinStatement_holds
        Classify.siegelGenStatement_holds
    have hSp : Stroth310SympBranchStatement :=
      stroth310SympBranch_of_steps h34 (stroth310SympForm_of_34 h34) hCl
    rcases hSp G M Q Z B hc n x hs5 hR hV with hsp | hΩ | hP
    · exact (false_of_spNat stroth34Statement_unconditional stroth311aStatement_unconditional
        stroth311bCommStatement_unconditional stroth51Statement_unconditional
        sec8AExistsStatement_unconditional stroth83Statement_holds stroth84Statement_holds
        cfg hxH hxQ hsp).elim
    · by_cases h2 : OmegaPlusNat hc x 2
      · exact h2
      · exact (false_of_omegaNat stroth34Statement_unconditional
          stroth311aStatement_unconditional stroth311bCommStatement_unconditional
          stroth311bCardStatement_unconditional stroth51Statement_unconditional
          sec7AExistsStatement_unconditional stroth78Statement_holds stroth79Statement_holds
          stroth711StrongStatement_holds sec7CentreMpStatement_holds sec7ZtStatement_holds
          sec79MinOrderStatement_holds sec717ZNStatement_holds step715ZNStatement_holds
          cfg hxH hxQ hΩ h2).elim
    · exact hP

end S93O

end Certs

end CFSG.RankThree.GF2n.Stroth80
