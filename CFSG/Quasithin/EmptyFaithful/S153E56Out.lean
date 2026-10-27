module

public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

section Out

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure Geom56Concl (cx : Ctx15350 T Mc M V₁ V₂ t) (s : ℕ) (y t₁ : G) : Prop where
  X_transv : IsFullTransvGroup153
    (autOn (tildeOf (quasithinOmegaOneCenter T) (Xgp153 T M V₁ Mc y))
      (tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)))
    ((tildeOf (quasithinOmegaOneCenter T)
        (quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y)).subgroupOf
      (tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)))
  dsum : tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc) =
      tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y) ⊔
        tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁) ∧
    tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y) ⊓
        tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁) = ⊥
  X_norm_Et : Xgp153 T M V₁ Mc y ≤
    Subgroup.normalizer (conjSubgroup (Egp153 T M V₁ Mc y) t₁ : Set G)
  X_axis : IsFullAxisGroup153
    (autOn (tildeOf (quasithinOmegaOneCenter T) (Xgp153 T M V₁ Mc y))
      (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁)))
    ((tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁ ⊓
        Subgroup.centralizer ((quasithinOmegaOneCenter T ⊔
          conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) : Set G))).subgroupOf
      (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁)))
  inter : XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y) ⊓
      XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁) =
    XStar153 T M V₁ Mc (VZ T M)
  card_Vstar : Nat.card (XStar153 T M V₁ Mc (VZ T M)) = 2
  D8s : IsD8Power153 s (XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y) ⊔
    XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁))
  fixed : ZS153 T M V₁ = centralizerMod (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)
    (Xgp153 T M V₁ Mc y ⊔ Subgroup.zpowers t₁)

end Out

end CFSG.Quasithin
