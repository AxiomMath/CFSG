module

public import CFSG.RankThree.PartTwo.Sec15.Item153TwinProof
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofOmega
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofA5
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofNorm
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofON
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofFaith
public import CFSG.RankThree.PartTwo.Sec17.RouteWireTop

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem claim153TwinR_of_items
    (h148 : Item148R) (h149 : Sec16.Item149S14) (h152 : Item152R) : Claim153TwinR :=
  claim153TwinR_of_twinX h149 h152
    (claim153TwinXR_of_norm h149 h152 (claim153TwinNormR_of h148 h149 h152))

theorem item153MainR_of_char
    (h148 : Item148R) (h149 : Sec16.Item149S14) (h152 : Item152R) (hchar : Claim153CharR) :
    Item153MainR :=
  item153MainR_of_twin h149 (claim153TwinR_of_items h148 h149 h152) hchar

theorem step153CharPush_of_charR (hchar : Claim153CharR) : Step153CharPush :=
  fun G _ _ A c L hR Y hY S hS hno => (hno (hchar G A c L hR Y hY S hS)).elim

theorem item156R_of_twin3
    (h148 : Item148R) (h152 : Item152R) (h149 : Sec16.Item149S14) (h315 : Item3_15)
    (h316 : Sec19.Item316) (h1411 : Item1411_1R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h142 : Item142AllS14) (hpush : Step153CharPush) (hONK : Step156ONKR)
    (hA5D : Step156CQA5DR) (hFN : Step156CQFaithfulNR) : Item156R :=
  item156R_of_q h148 h152
    (claim156QR_of_twin h149 (claim153TwinR_of_items h148 h149 h152) h315 h316 hpush) h1411
    h134 h48 h142 (step156ONXR_of h148 h134 h48 (step156ONXKR_of_onk h152 hONK))
    (step156CQA5R_of h134 h48 h142 h152 hA5D) (step156CQOmegaR_of h134 h48)
    (step156CQFaithfulR_of h142 hFN)

theorem claim153NoTwinA5A6_of_small
    (h148 : Item148R) (h152 : Item152R) (hq : Claim156QR) (h1411 : Item1411_1R)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Item142AllS14) (hA5 : Step156CQA5R)
    (hΩ : Step156CQOmegaR) (hP : Step156CQFaithfulR) : Claim153NoTwinA5A6 := by
  intro G _ _ A c L hR Y hY _ htype M _
  exfalso
  have h := hR.toSec14Std
  obtain ⟨c₀, L₀, d, X₁, D⟩ := exists_data156_of_small' h (h148 G A c L hR) h134 h48
    Sec4.Sporadic.rank3II_4_15 (step156DR_of h142 G A c L hR) hY htype
  have htype' : IsType156 Y := by
    rcases htype with he | h6
    · exact Or.inl he
    · exact Or.inr (Or.inl h6)
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := D.omega, mem_lA := D.mem_lA }
  by_cases hΩA : omegaA A = {Subgroup.zpowers c₀}
  · obtain ⟨M', hM', S, hS, hSM⟩ := hq G A c L hR Y hY htype'
    exact Proof153Twin.false_of_omegaA_eq_of_le h142 h₀ (h152 G A c L hR) (h1411 G A c L hR) hY
      htype' D hΩA hM' hS hSM
  · exact false_of_omegaA_ne h₀ (step156CQR_of_faithful h142 h134 h48 hA5 hΩ hP G A c L hR) hY
      htype' D hΩA

theorem claim153NormalR_of_twin3_small
    (h148 : Item148R) (h152 : Item152R) (h149 : Sec16.Item149S14) (h315 : Item3_15)
    (h316 : Sec19.Item316) (h1411 : Item1411_1R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h142 : Item142AllS14) (hpush : Step153CharPush) (hA5D : Step156CQA5DR)
    (hFN : Step156CQFaithfulNR) : Claim153NormalR :=
  claim153NormalR_of_wired h152
    (claim153NormalNoE9R_of
      (claim153TwinTypes_of h148 h149 h152 (claim153TwinCase7_of h149 h152))
      (claim153NoTwinA5A6_of_small h148 h152
        (claim156QR_of_twin h149
          (claim153TwinR_of_twinX h149 h152
            (claim153TwinXR_of_norm h149 h152 (claim153TwinNormR_of h148 h149 h152)))
          h315 h316 hpush)
        h1411 h134 h48 h142 (step156CQA5R_of h134 h48 h142 h152 hA5D) (step156CQOmegaR_of h134 h48)
        (step156CQFaithfulR_of h142 hFN)))

theorem item156R_of_twin3_meet
    (h148 : Item148R) (h152 : Item152R) (h149 : Sec16.Item149S14) (h315 : Item3_15)
    (h316 : Sec19.Item316) (h1411 : Item1411_1R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h142 : Item142AllS14) (hpush : Step153CharPush) (hONK : Step156ONKR)
    (hA5D : Step156CQA5DR) (hMF : Step156QThetaMeetR) : Item156R :=
  item156R_of_twin3 h148 h152 h149 h315 h316 h1411 h134 h48 h142 hpush hONK hA5D
    (step156CQFaithfulNR_of_meet h134 h48 h142 hMF)

theorem claim153NormalR_of_twin3_meet
    (h148 : Item148R) (h152 : Item152R) (h149 : Sec16.Item149S14) (h315 : Item3_15)
    (h316 : Sec19.Item316) (h1411 : Item1411_1R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h142 : Item142AllS14) (hpush : Step153CharPush) (hA5D : Step156CQA5DR)
    (hMF : Step156QThetaMeetR) : Claim153NormalR :=
  claim153NormalR_of_twin3_small h148 h152 h149 h315 h316 h1411 h134 h48 h142 hpush hA5D
    (step156CQFaithfulNR_of_meet h134 h48 h142 hMF)

end CFSG.RankThree.PartTwo.Sec15
