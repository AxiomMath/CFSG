module

public import CFSG.Quasithin.EmptyFaithful.T1531Stage1
public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.ThreePrimeGroup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

structure Res15346 {G : Type} [Group G] (T M V₁ V₂ : Subgroup G) : Prop where
  fusion : ∀ x ∈ VZ T M, ∀ g : G, g * x * g⁻¹ ∈ VZ T M →
    ∃ m ∈ M, m * x * m⁻¹ = g * x * g⁻¹
  totSingular_inter : ∀ g : G, g ∉ M →
    IsTotSingular153 T M V₁ V₂ (VZ T M ⊓ conjSubgroup (VZ T M) g)
  totSingular_of_normalizer : ∀ U : Subgroup G, U ≤ VZ T M → ⊥ < U → U < VZ T M →
    ¬ Subgroup.normalizer (U : Set G) ≤ M → IsTotSingular153 T M V₁ V₂ U
  one_lt_r : 1 < E3.rParam (VZ T M)
  w0_centralizes : E3.wClos (VZ T M) 0 T ≤ Subgroup.centralizer (VZ T M : Set G)
  w_pos : 0 < E3.wParam T (VZ T M)
  conj_le_centralizer : ∀ g : G, conjSubgroup (VZ T M) g ≤ M →
    conjSubgroup (VZ T M) g ≤ Subgroup.centralizer (VZ T M : Set G)
  normalizer_w0 : Subgroup.normalizer (E3.wClos (VZ T M) 0 T : Set G) ≤ M
  normalizer_ZS : Subgroup.normalizer (ZS153 T M V₁ : Set G) ≤ M
  centralizer_nonsingular : ∀ v : G, v ≠ 1 → (v ∈ V₁ ∨ v ∈ V₂) →
    Subgroup.centralizer ({v} : Set G) ≤ M

@[expose] def Stage15346 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂

@[expose] def Res15347 {G : Type} [Group G] (T M V₁ : Subgroup G) : Prop :=
  ∀ x ∈ Subgroup.centralizer (ZS153 T M V₁ : Set G),
    ⁅VZ T M, Subgroup.zpowers x⁆ = ⊥ ∨
      ∀ g : G, conjSubgroup (VZ T M) g ≤
        Subgroup.normalizer ((⁅VZ T M, Subgroup.zpowers x⁆ : Subgroup G) : Set G) →
          conjSubgroup (VZ T M) g ≤ Subgroup.centralizer (VZ T M : Set G)

@[expose] def Stage15347 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15347 T M V₁

@[expose] def Stage15348 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15347 T M V₁ →
      ∀ H : Subgroup G, IsHTM153 T M H →
        (Case157Two T Mc M → Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ H) →
          HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H

structure Res15349 {G : Type} [Group G] (T Mc M V₁ : Subgroup G) : Prop where
  oTwoUpper_le : ∀ H : Subgroup G, IsHTM153 T M H →
    oTwoUpper (M ⊓ H) ≤ Subgroup.centralizer (VZ T M : Set G)
  comm_ZS : ⁅ZS153 T M V₁, pCoreOf 2 Mc⁆ = quasithinOmegaOneCenter T
  case_one : Case157One T Mc M
  pCore_eq_centralizer_Z : pCoreOf 2 (Y153 Mc M) =
    Y153 Mc M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  eq_oPrime : Y153 Mc M = oPrimeResidualOf 3 M
  threePrime_C : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (VZ T M : Set G))
  threePrime_MH : ∀ H : Subgroup G, IsHTM153 T M H → IsThreePrimeGroup (M ⊓ H)
  normalizer_ZS_eq : Subgroup.normalizer (ZS153 T M V₁ : Set G) =
    M ⊓ Subgroup.normalizer (ZS153 T M V₁ : Set G)
  threePrime_N : IsThreePrimeGroup (Subgroup.normalizer (ZS153 T M V₁ : Set G))

@[expose] def Stage15349 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15347 T M V₁ →
      (∀ H : Subgroup G, IsHTM153 T M H →
        (Case157Two T Mc M → Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ H) →
          HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H) →
      Res15349 T Mc M V₁

end CFSG.Quasithin
