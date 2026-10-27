module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def SubConfigSatz (M Q Z N : Subgroup G) : Prop :=
  SubConfig M Q Z N ∧
  ∃ hN : (Q.subgroupOf (H0 M Z)).Normal, haveI := hN
    ∀ B₂ : Subgroup (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)),
      Ctx (Subgroup.normalizer ((cen (bar (H0 M Z) Q N) : Subgroup _) : Set _))
        (bar (H0 M Z) Q N) (cen (bar (H0 M Z) Q N)) B₂ →
      StrothConclusion (Subgroup.normalizer ((cen (bar (H0 M Z) Q N) : Subgroup _) : Set _))
        (bar (H0 M Z) Q N) (cen (bar (H0 M Z) Q N)) B₂

@[expose] def Stroth121SpCoreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Stroth12Hyp hc n → ∀ t ∈ LB M Q B, t ∉ Q → Conc83 hc n t →
    SubConfigSatz M Q Z (hc.CN t) → False

@[expose] def Stroth121OmegaCoreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Stroth12Hyp hc n → ∀ t ∈ LB M Q B, t ∉ Q → OmegaExcluded hc n t → Conc79 hc n t →
    SubConfigSatz M Q Z (hc.CN t) → False

end CFSG.RankThree.GF2n.Stroth80
