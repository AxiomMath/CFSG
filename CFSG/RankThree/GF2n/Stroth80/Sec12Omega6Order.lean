module

public import CFSG.RankThree.GF2n.Stroth80.Sec12OrderBelow
public import CFSG.RankThree.GF2n.Stroth80.Sec12FStarIii
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Sec12Omega6PlusStepBBelow
public import CFSG.RankThree.GF2n.Stroth80.Sec12Omega6PlusCaseE6

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

section Omega6


@[expose] def Stroth12Omega6OrderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    CFSG.RankThree.GF2n.Smith81.Smith1981TheoremBelow (Nat.card G) →
    Stroth1980Below (Nat.card G) → Stroth12Hyp hc n → ∀ t ∈ LB M Q B, t ∉ Q →
    (OmegaPlusNat hc t 3 ∨ OmegaMinusNat hc t 3) → SubConfig M Q Z (hc.CN t) →
    Sec12Iii M Q Z (Lgen M (LB M Q B))

theorem stroth12Omega6_of_order_core
    (hm : Stroth12Omega6MinusStatement) (hA : Stroth12Omega6PlusCaseE6Statement)
    (hq : Sec12Omega6PlusQStatement) (hF : Stroth12FStarIiiStatement) :
    Stroth12Omega6OrderStatement := by
  intro G _ _ M Q Z B hc n hM hS hhyp t ht htQ htype hsub
  haveI := hc.normal_Q_in_M
  have hsubS := hsub.satz_of_orderBelow hc.hyp hS
  rcases htype with h | h
  · refine hF G M Q Z B hc n hhyp t ht htQ (Or.inr ⟨h, ?_⟩)
    exact stroth12Omega6PlusStepB_of_below (SmithE6FourClauseBelow_of_smith1981 hM) hq G
      (Nat.lt_succ_self _) M Q Z B hc n hhyp t ht htQ h hsubS
      (hA G M Q Z B hc n hhyp t ht htQ h hsubS)
  · exact (hm G M Q Z B hc n hhyp t ht htQ h hsubS).elim

end Omega6

end CFSG.RankThree.GF2n.Stroth80
