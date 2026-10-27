module

public import CFSG.Quasithin.MS93.S38PU
public import CFSG.Quasithin.MS93.SkItems

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open scoped commutatorElement

@[expose] def XOffCent {G : Type} [Group G] (M T : Subgroup G) : Prop :=
  ∀ F : Subgroup G, IsXOff M T F → T ⊓ Subgroup.centralizer (F : Set G) ≤ F ⊔ pCoreOf 2 M

@[expose] def XOffCentU {G : Type} [Group G] (M T L : Subgroup G) : Prop :=
  ∀ F : Subgroup G, IsXOff M T F → ∀ y ∈ T, y ∈ Subgroup.centralizer (F : Set G) →
    (∀ u ∈ Uq M T L, ⁅u, y⁆ ∈ Subgroup.centralizer (F : Set G)) → y ∈ F ⊔ pCoreOf 2 M

theorem XOffCent.xOffCentU {G : Type} [Group G] {M T : Subgroup G} (hC : XOffCent M T)
    (L : Subgroup G) : XOffCentU M T L :=
  fun F hF _ hyT hyC _ => hC F hF ⟨hyT, hyC⟩

@[expose] def S38End : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    T ⊓ Subgroup.centralizer (Z0q M T : Set G) = pCoreOf 2 M → ⁅Xq M, L⁆ ≤ Uq M T L →
    (IsHatA6U M T L ∨ IsDoubleSL3U M T L ∨ IsSL3TwoU M T L ∨ IsSL3TwoZ M T L ∨
      IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1) →
    ¬ IsSL3U M T L → ¬ IsSp4U M T L → XOffData M T → XOffCentU M T L →
    ((∀ F : Subgroup G, IsXOff M T F → (pCoreOf 2 M).relIndex F ≤ 4) ∨ IsDoubleSL3U M T L) →
    critDist (puAmalgam h.le) = 4 →
    (∀ ε ε' : Vtx (puAmalgam h.le), IsCritical _ ε ε' →
      stab _ (geo _ ε ε' 2) ≤ Subgroup.normalizer
        ((⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆ :
          Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) ∧
      puTrans h.le L (geo _ ε ε' 2) ≤ Subgroup.centralizer
        ((⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆ :
          Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal)) →
    (∀ ε ε' : Vtx (puAmalgam h.le), IsCritical _ ε ε' →
      ¬ Vv (puAmalgam h.le) ε ≤ Qv (puAmalgam h.le) (geo _ ε' ε 2)) →
    False

@[expose] def S38G2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    T ⊓ Subgroup.centralizer (Z0q M T : Set G) = pCoreOf 2 M → ⁅Xq M, L⁆ ≤ Uq M T L →
    IsG2U h.le L → 2 < critDist (puAmalgam h.le) → False

end CFSG.Quasithin.MS93
