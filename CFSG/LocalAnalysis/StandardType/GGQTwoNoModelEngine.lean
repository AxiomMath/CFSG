module

public import CFSG.LocalAnalysis.StandardType.GGWAutProp898
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGQTwoReduction

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

@[expose] def GGQ2NoModelEngineSel {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (Bs : Subgroup G) : Prop :=
  GGQ2ReflAbsIrred p Bs ∧ ∃ m : ℕ, 5 ≤ m ∧ Nat.card Bs = p ^ m ∧
    (Even m → ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V),
      ¬ GGOrthType ((ggReflGp p Bs).map (ggLin (p := p) ι)))

@[expose] def GGQ2NoModelRest2Input : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J →
      (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        ¬ Nonempty (GGQTwoModel p Bs x y D L J K)) →
      ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      ¬ GGQTwoTwoNodeRowAt p L J → ¬ GGQTwoTwoNodeRowAt p K J →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ¬ GGQ2NoModelEngineSel p Bs →
      Subgroup.centralizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) →
      (∀ u : ↥Bs, (u : G) ∈ D → u ≠ 1 → GGGammaAt p B Bs x L D J u) →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGQ2NoModelEngineCell : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J →
      (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        ¬ Nonempty (GGQTwoModel p Bs x y D L J K)) →
      ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      ¬ GGQTwoTwoNodeRowAt p L J → ¬ GGQTwoTwoNodeRowAt p K J →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      GGQ2NoModelEngineSel p Bs →
      Subgroup.centralizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) →
      (∀ u : ↥Bs, (u : G) ∈ D → u ≠ 1 → GGGammaAt p B Bs x L D J u) →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

theorem ggQ2_noModel_engineCell (hE : GGWAutEngine) : GGQ2NoModelEngineCell := by
  intro G _ _ p _ hp B Bs x L D J hS hI hnomod y K hnb h1 h2 hW hsel hC hΓ
  subst hp
  obtain ⟨hAbs, m, hm5, hm, hNO⟩ := hsel
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨-, hBstar, hStdSub⟩ := hcfg
  have hDBs : D ≤ Bs := hStdSub.1.1.trans hBstar.1
  have hxD : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert x {y})
  have hxne : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  exact ggQ2_reduction hS hC hΓ ⟨⟨x, hDBs hxD⟩, hxD, fun h => hxne (Subtype.ext_iff.mp h),
    ggQ2_orbitStable_of_engine hE hS.1.2.2.2.1 hAbs hm5 hm hNO _⟩

theorem ggQ2_noModel_of_rest2_cell (hr : GGQ2NoModelRest2Input) (hc : GGQ2NoModelEngineCell) :
    GGQ2NoModelInput := by
  intro G _ _ p _ hp B Bs x L D J hS hI hnomod y K hnb h1 h2 hW hC hΓ
  by_cases hsel : GGQ2NoModelEngineSel p Bs
  · exact hc hp hS hI hnomod hnb h1 h2 hW hsel hC hΓ
  · exact hr hp hS hI hnomod hnb h1 h2 hW hsel hC hΓ

end CFSG.StandardType

end
