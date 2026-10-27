module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem16A8Zv

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Lem12216A8VvComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z v g : G), Hyp1223 G T L V →
    NoEscape12_2_13 L V →
    (∃ _ : IsMulCommutative ↥V, (altCoreModel 8).Realizes (autOn L V) ⊤ ⊥) →
    V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers z → z ≠ 1 →
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) →
    v ∈ V → v ∉ Subgroup.zpowers z → g ∉ Subgroup.normalizer (L : Set G) →
    g⁻¹ * v * g = v * z →
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G)) (Subgroup.centralizer ({v} : Set G)) →
    g ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) →
      ⁅conjClosure (quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer ({v} : Set G))) L, L⁆ = V

@[expose] def Lem12216A8VvFix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z v g : G), Hyp1223 G T L V →
    NoEscape12_2_13 L V →
    (∃ _ : IsMulCommutative ↥V, (altCoreModel 8).Realizes (autOn L V) ⊤ ⊥) →
    V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers z → z ≠ 1 →
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) →
    v ∈ V → v ∉ Subgroup.zpowers z → g ∉ Subgroup.normalizer (L : Set G) →
    g⁻¹ * v * g = v * z →
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G)) (Subgroup.centralizer ({v} : Set G)) →
    g ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) →
    ⁅conjClosure (quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer ({v} : Set G))) L, L⁆ = V →
      ∀ x ∈ T ⊓ Subgroup.centralizer ({v} : Set G),
        x ∈ Subgroup.centralizer ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) →
          x ^ 2 = 1 → ∃ a ∈ V, a ∈ Subgroup.centralizer
            ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) ∧
            ∃ b ∈ T ⊓ Subgroup.centralizer ({v} : Set G), b ∈ Subgroup.centralizer
              ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) ∧
              b ∈ Subgroup.centralizer (L : Set G) ∧ x = a * b

theorem lem12216A8Zv_of (hc : Lem12216A8VvComm) (hf : Lem12216A8VvFix) : Lem12216A8Zv :=
  fun G _ _ T L V z v g hH hNE hmod hVL hz1 hNV hvV hvz hgM hgv hsyl hgN =>
    hf G T L V z v g hH hNE hmod hVL hz1 hNV hvV hvz hgM hgv hsyl hgN
      (hc G T L V z v g hH hNE hmod hVL hz1 hNV hvV hvz hgM hgv hsyl hgN)

end CFSG.Quasithin.H13
