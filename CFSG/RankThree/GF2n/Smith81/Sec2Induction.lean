module

public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Smith81.ELane
public import CFSG.RankThree.GF2n.Smith81.LinLane
public import CFSG.RankThree.GF2n.Smith81.OrthLane

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

@[expose] def LaneTIStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Smith1981Below (Nat.card G) →
    ∀ (M Q Z : Subgroup G), StrothHyp M Q Z →
      ∀ B : Subgroup G, (∃ g : G, B = conjSubgroup g Z) → B ≤ Q → B ≠ Z →
        StrothConclusion M Q Z B → SmithLaneTI M Q Z B

theorem laneTIStep_of_inputs (hCorB : CorBRankTwo)
    (hOrd : TiLieOrders) (hD2 : TiFusionD2Statement) (hD3 : TiFusionD3Statement)
    (hLin : TiLinearD2Step) : LaneTIStep := by
  intro G _ _ hb M Q Z hH B hB hBQ hBZ _
  exact ⟨fun n hn => smithLaneTI_D1 hCorB hOrd hH hn,
    fun hc => ⟨smithLaneTI_D2 hCorB hOrd hD2 hH hB hBQ hBZ hc,
      hLin G hb M Q Z B hH hB hBQ hBZ hc⟩,
    smithLaneTI_D3 hCorB hOrd hD3 hH hB hBQ hBZ⟩

theorem smith1981_of_steps (hTI : LaneTIStep) (hOrth : LaneOrthStep) (hE : LaneEStep)
    (hLin : LaneLinStep) (h216 : Smith216Statement) : Smith1981Statement := by
  refine smith1981_of_below fun N hb => hb.succ ?_ ?_
  · intro G _ _ hG M Q Z hH B hB hBQ hBZ hC
    have hb' : Smith1981Below (Nat.card G) := by rw [hG]; exact hb
    exact (smithConclusion_iff_lanes M Q Z B).mpr
      ⟨hTI G hb' M Q Z hH B hB hBQ hBZ hC, hOrth G hb' M Q Z hH B hB hBQ hBZ hC,
        hE G hb' M Q Z hH B hB hBQ hBZ hC, hLin G hb' M Q Z hH B hB hBQ hBZ hC⟩
  · intro G _ _ hG
    have hb' : Smith216Below (Nat.card G) := by rw [hG]; exact hb.2
    exact smith216At_of_statement h216 hb'

end CFSG.RankThree.GF2n.Smith81
