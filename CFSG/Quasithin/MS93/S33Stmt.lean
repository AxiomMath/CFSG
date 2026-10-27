module

public import CFSG.Quasithin.MS93.SkItems

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ

@[expose] def S33Bad : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    critDist (puAmalgam h.le) = 2 → ⁅Xq M, L⁆ ≤ Uq M T L →
    (IsHatA6U M T L ∨ IsDoubleSL3U M T L ∨ IsSL3TwoU M T L ∨ IsSL3TwoZ M T L ∨ IsG2U h.le L) →
    ¬ IsSL3U M T L → (∀ k, ¬ IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k) →
    ∀ α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) (baseA _) α' →
    ∀ Y : Subgroup (puAmalgam h.le).Universal, Y ≤ Qv _ (geo _ α' (baseA _) 1) →
      Y ≤ Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal) →
      Y ≤ Subgroup.centralizer (XM (puAmalgam h.le) (baseA _) : Set (puAmalgam h.le).Universal) →
      ¬ ⁅ZM (puAmalgam h.le) α', Y⁆ ≤
          ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
            ⁅critA (puAmalgam h.le) (baseA _) α', Y⁆ → False

@[expose] def S33Hyp {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
    (α' : Vtx (puAmalgam h.le)) (Y : Subgroup (puAmalgam h.le).Universal) : Prop :=
  IsCritical (puAmalgam h.le) (baseA _) α' ∧ Y ≤ Qv _ (geo _ α' (baseA _) 1) ∧
    Y ≤ Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal) ∧
    ¬ ⁅ZM (puAmalgam h.le) α', Y⁆ ≤
        ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
          ⁅critA (puAmalgam h.le) (baseA _) α', Y⁆

@[expose] def S33LW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    ⁅Xq M, L⁆ ≤ Uq M T L → ∀ k, IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k →
    ∀ (α' : Vtx (puAmalgam h.le)) (Y : Subgroup (puAmalgam h.le).Universal), S33Hyp h α' Y →
      2 ^ (2 * k) ≤ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) →
      k = 1 ∧ ∃ t₁ ∈ Qv _ (geo _ α' (baseA _) 1), ∃ t₂ ∈ Qv _ (geo _ α' (baseA _) 1),
        (∀ t ∈ ({t₁, t₂} : Set (puAmalgam h.le).Universal),
          (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal)).relIndex (ZM _ α') = 2) ∧
        t₁ * t₂⁻¹ ∉ Qv _ α' ∧
        ZM _ (baseA _) ⊔ Qv _ α' =
          Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α'

end CFSG.Quasithin.MS93.S33
