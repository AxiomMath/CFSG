module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Induction
public import CFSG.RankThree.GF2n.Smith81.ERecursion

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

section Satz

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem SubConfig.satz_of_orderBelow {N : Subgroup G} (H : StrothHyp M Q Z)
    (h : SubConfig M Q Z N) (hn : Stroth1980Below (Nat.card G)) : SubConfigSatz M Q Z N := by
  obtain ⟨hN, hsub⟩ := h
  haveI := hN
  refine ⟨⟨hN, hsub⟩, hN, fun B₂ hB₂ => ?_⟩
  exact hn _ (CFSG.RankThree.GF2n.Smith81.card_H0_quot_lt H) _ _ _ hB₂.hyp B₂ hB₂.conj hB₂.le
    hB₂.ne

end Satz

section Order


@[expose] def Stroth121SpOrderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Stroth1980Below (Nat.card G) → Stroth12Hyp hc n → ∀ t ∈ LB M Q B, t ∉ Q → Conc83 hc n t →
    SubConfig M Q Z (hc.CN t) → False

theorem stroth121Sp_of_order_core (hC : Stroth121SpCoreStatement) :
    Stroth121SpOrderStatement := by
  intro G _ _ M Q Z B hc n hbelow hhyp t ht htQ h83 hsub
  exact hC G M Q Z B hc n hhyp t ht htQ h83 (hsub.satz_of_orderBelow hc.hyp hbelow)

@[expose] def Stroth121OmegaOrderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Stroth1980Below (Nat.card G) → Stroth12Hyp hc n → ∀ t ∈ LB M Q B, t ∉ Q →
    OmegaExcluded hc n t → SubConfig M Q Z (hc.CN t) → Conc79 hc n t → False

theorem stroth121Omega_of_order_core (hC : Stroth121OmegaCoreStatement) :
    Stroth121OmegaOrderStatement := by
  intro G _ _ M Q Z B hc n hbelow hhyp t ht htQ hex hsub h79
  exact hC G M Q Z B hc n hhyp t ht htQ hex h79 (hsub.satz_of_orderBelow hc.hyp hbelow)

end Order

end CFSG.RankThree.GF2n.Stroth80
