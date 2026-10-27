module

public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.H13.L32A71

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace L32A

variable {G : Type} [Group G]

@[expose] def u0 (T V : Subgroup G) : Subgroup G :=
  centralizerMod (fsuV1 T V) (fsuU T V) (kz T V)

end L32A

@[expose] def Lemma14_7_38 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g →
      F8.Dγ V (fsuV1 T V) H (g : G) < F8.Uγ V H (g : G)

@[expose] def Lemma14_7_67 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    (∀ V₂ : Subgroup G, A6.IsV2 T V V₂ →
      Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
    (∀ F : Subgroup G, F ≤ V → Nat.card F = 4 → ∀ g : G, F ≤ conjSub g V → conjSub g V = V) ∧
    quasithinIsMaximalLocal T (L32A.kz T V) ∧
    (Subgroup.normalizer (L32A.kz T V : Set G) = L32A.hz T V ∧
      quasithinIsMaxTwoLocal (L32A.hz T V)) ∧
    L ⊔ T = Subgroup.normalizer (V : Set G)

@[expose] def Lemma14_7_68 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    (∀ z ∈ fsuV1 T V, ∀ g : G, g * z * g⁻¹ ∈ L32A.u0 T V → g * z * g⁻¹ = z) ∧
    ∀ u ∈ L32A.u0 T V, u ≠ 1 → (∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) →
      Subgroup.centralizer ({u} : Set G) ≤ L32A.hz T V ∧
        ∀ g : G, u ∈ conjSub g (L32A.u0 T V) → conjSub g (L32A.u0 T V) = L32A.u0 T V

@[expose] def Lemma14_7_69 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    ∀ (γ γ' : F8.Geom T L (L32A.hz T V)) (g h : ↥((L ⊔ T) ⊔ L32A.hz T V)),
      L32A.Not1471 T L V (L32A.hz T V) γ γ' g h →
      (pCoreOf 2 (L32A.hz T V)).relIndex
        (conjSub (h : G) (F8.Uγ V (L32A.hz T V) (g : G)) ⊔ pCoreOf 2 (L32A.hz T V)) = 2

@[expose] def Lemma14_7_70 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    Nat.card ↥(L32A.u0 T V) ≤ 4 ∧
    ∃ (γ γ' : F8.Geom T L (L32A.hz T V)) (g h : ↥((L ⊔ T) ⊔ L32A.hz T V)) (V₂ : Subgroup G),
      L32A.Not1471 T L V (L32A.hz T V) γ γ' g h ∧ A6.IsV2 T V V₂ ∧
      conjSub (h : G) (F8.A₁ (fsuV1 T V) (g : G)) ≤ V₂ ∧
      fsuU T V ⊓ conjSub (h : G) (F8.Uγ V (L32A.hz T V) (g : G)) = V ⊔ L32A.u0 T V ∧
      V ⊔ L32A.u0 T V = ⁅fsuU T V, conjSub (h : G) (F8.Uγ V (L32A.hz T V) (g : G))⁆ ⊔ V ∧
      ⁅fsuU T V, conjSub (h : G) (F8.Uγ V (L32A.hz T V) (g : G))⁆ ⊔ V =
        ⁅fsuU T V, conjSub (h : G) (F8.Uγ V (L32A.hz T V) (g : G))⁆ ⊔ L32A.u0 T V ∧
      F8.b T V L (L32A.hz T V) = 3 ∧
      ∃ l ∈ L, conjSub (h : G) (F8.Uγ V (L32A.hz T V) (g : G)) = conjSub l (fsuU T V)

@[expose] def Lemma14_7_71 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    (L32A.IsL24Section (L32A.kz T V) (pCoreOf 2 (L32A.hz T V))
        (pCoreOf 2 (L32A.hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) ∧
      ⁅pCoreOf 2 (L32A.hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G), L32A.kz T V⁆ ≤
        fsuU T V) ∧
    (∀ x ∈ L₁Of L (fsuV1 T V), x ^ 3 = 1 → x ≠ 1 →
      (Subgroup.centralizer ({x} : Set G) ⊓ pCoreOf 2 (L₁Of L (fsuV1 T V))).relIndex
          (pCoreOf 2 (L₁Of L (fsuV1 T V))) = 4 ^ 5 ∧
        (Subgroup.centralizer ({x} : Set G) ⊓ L32A.sL T L V).relIndex (L32A.sL T L V) = 4 ^ 4) ∧
    ⁅pCoreOf 2 (L ⊔ T), L⁆ ≤ L32A.sL T L V

end CFSG.Quasithin.H13
