module

public import CFSG.Quasithin.Background.GoldschmidtTDE68L2pSmall

public section

namespace CFSG.Quasithin.E6

open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.Quasithin.E6.Bar
  CFSG.ComponentClassification.CatLeaf CFSG.Assembly.LowTwoRank

theorem e68CentCompL2p_holds : E68CentCompL2p := by
  intro Y _ _ L R K z u hE h hK
  exfalso
  obtain ⟨hmodel, -⟩ := hE
  have key : IsSimpleGroup ↥L ∧ SylowCentralizingAutInner ↥L ∧
      InvolutionCentralizersComponentFree ↥L := by
    rcases hmodel with h33 | ⟨p, hFM, hp⟩
    · exact ⟨(CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 3 1 h33).2,
        L2p.psl3_three_facts h33⟩
    · obtain ⟨hprime, -, -, h22, h23⟩ := hp.1
      have hsimple := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hp).2
      have h2 := hprime.two_le
      by_cases h7 : 7 ≤ p
      · exact ⟨hsimple, L2p.psl2_facts hFM h7 hp⟩
      · have h5 : p = 5 := by
          have hp6 : p ≠ 6 := by
            rintro rfl
            norm_num at hprime
          have hp4 : p ≠ 4 := by
            rintro rfl
            norm_num at hprime
          have hp3 : p ≠ 3 := by
            rintro rfl
            exact h23 rfl
          have hp2 : p ≠ 2 := by
            rintro rfl
            exact h22 rfl
          omega
        subst h5
        exact ⟨hsimple, L2p.psl2_five_facts hp⟩
  obtain ⟨hs, hfix, hfree⟩ := key
  have hc : center ↥L = ⊥ := Inn.center_eq_bot_of_isQuasisimple_of_simple h.quasisimple hs
  let e : Qbar L ≃* ↥L := (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact Inn.not_isComponentIn_of_fix_free h
    (Inn.InvolFixInner.of_forall (SylowCentralizingAutInner.of_mulEquiv e hfix))
    (InvolutionCentralizersComponentFree.of_mulEquiv e hfree) K hK

end CFSG.Quasithin.E6
