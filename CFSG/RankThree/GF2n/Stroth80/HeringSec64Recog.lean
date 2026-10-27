module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec64Cor

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

namespace HS6


@[expose] def Stroth64RecogStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Stroth6Hyp hc n t → ∀ m : ℕ, 3 ≤ m → (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) →
    ∀ [(Q.subgroupOf M).Normal], CorBHyp (bar M Q (hc.CN t)) → CorollaryBStmt →
      QuotSat (Lgen M (hc.CN t)) Q (IsSLModel 2 (Nat.card Z))

theorem stroth64_of_recog_of_corBHyp (hA : Stroth64CorBHypStatement) (hB : CorollaryBStmt)
    (hR : Stroth64RecogStatement) : Stroth64Statement := by
  intro G _ _ M Q Z B hc n t hs m hm hΩ
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  exact hR G M Q Z B hc n t hs m hm hΩ (hA G M Q Z B hc n t hs m hm hΩ) hB

end HS6

section Certs

theorem stroth64_of_recog (hB : CorollaryBStmt) (hR : HS6.Stroth64RecogStatement) :
    Stroth64Statement :=
  HS6.stroth64_of_recog_of_corBHyp stroth64CorBHyp_holds hB hR

end Certs

end CFSG.RankThree.GF2n.Stroth80
