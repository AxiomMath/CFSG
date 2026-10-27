module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec1Thm

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lem1211He : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) (β : G → G → ZMod 2),
    Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) →
    IsDualPairing121 L V₁ V₂ β → ∀ v ∈ V, IsNonsingular121 V₁ V₂ β v →
      CharTwo (Subgroup.centralizer ({v} : Set G))

@[expose] def Lem1211Normal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) (β : G → G → ZMod 2),
    Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) →
    IsDualPairing121 L V₁ V₂ β → ∀ v ∈ V, IsNonsingular121 V₁ V₂ β v →
      CharTwo (Subgroup.centralizer ({v} : Set G)) →
      Subgroup.centralizer ({v} : Set G) ≤
        Subgroup.normalizer (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G)) : Set G) →
      Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lem1211NotNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) (β : G → G → ZMod 2),
    Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) →
    IsDualPairing121 L V₁ V₂ β → ∀ v ∈ V, IsNonsingular121 V₁ V₂ β v →
      CharTwo (Subgroup.centralizer ({v} : Set G)) →
      ¬ Subgroup.centralizer ({v} : Set G) ≤
        Subgroup.normalizer (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G)) : Set G) →
      Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G)

theorem lem1211_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (hHe : Lem1211He)
    (hN : Lem1211Normal) (hNN : Lem1211NotNormal) : Lem1211 := by
  intro G _ _ T L V V₁ V₂ n β hyp hβ v hv hns
  obtain ⟨hTL, -⟩ := Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp
  have he := hHe G T L V V₁ V₂ n β hyp hTL hβ v hv hns
  by_cases hnorm : Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.normalizer (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G)) : Set G)
  · exact hN G T L V V₁ V₂ n β hyp hTL hβ v hv hns he hnorm
  · exact hNN G T L V V₁ V₂ n β hyp hTL hβ v hv hns he hnorm

end CFSG.Quasithin.H13
