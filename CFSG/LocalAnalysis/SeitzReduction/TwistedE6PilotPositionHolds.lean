module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviAutSp

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem leviAutConj_leviX [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) : LeviAutConj (leviX σ) (thetaJ k σ) :=
  leviAutConj_of_isAutConjIn fun κ => match κ with
    | 0 => isAutConjIn_levi_tX hf hK hσ hk
    | 1 => isAutConjIn_levi_uX hf hk hK hσ

theorem leviAutConj_leviY [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) : LeviAutConj (leviY σ) (shortJ k σ) :=
  leviAutConj_of_isAutConjIn fun κ => match κ with
    | 0 => isAutConjIn_levi_tY hf hK hσ hk
    | 1 => isAutConjIn_levi_uY hf hk hK hσ

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_neighbour_2E6_X_holds (hset : SeitzSetting G L) [CharP K 2] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    {X : Subgroup G} (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal :=
  not_normal_neighbour_2E6_X hset hf2 hk hK hσ e htC ht hξ
    (leviAutConj_leviX (by omega) hk hK hσ) hX hDe

theorem not_normal_neighbour_2E6_Y_holds (hset : SeitzSetting G L) [CharP K 2] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    (hT : TorusConjY k σ)
    {X : Subgroup G} (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal :=
  not_normal_neighbour_2E6_Y hset hf2 hk hK hσ e htC ht hξ
    (leviAutConj_leviY (by omega) hk hK hσ) hT hX hDe

end CFSG.SeitzReduction.TwistedE6Pilot
