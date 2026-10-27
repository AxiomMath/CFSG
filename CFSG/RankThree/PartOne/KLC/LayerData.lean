module

public import CFSG.RankThree.PartOne.S11d.LayerDecomp
public import CFSG.RankThree.PartOne.S11d.LieCentralizerTags
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion

public section

namespace CFSG.RankThree.PartOne.KLC

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag)

open CFSG.Blueprint (LieModel)

open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix

@[expose] def LieLayerData (p : ℕ) {G : Type} [Group G] (α : MulAut G) (X : Subgroup G) : Prop :=
  ∃ (ι : Type) (Q : ι → Subgroup G), Nonempty ι ∧ (∀ i, IsComponentOf X (Q i)) ∧
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer ((⨆ i, Q i : Subgroup G) : Set G)) ∧
    ((⨆ i, Q i : Subgroup G).subgroupOf X).Normal ∧
    Odd ((⨆ i, Q i : Subgroup G).subgroupOf X).index ∧
    ∀ i, (∀ g ∈ Q i, α g ∈ Q i) →
      (∀ e ∈ Q i, ¬ ∀ g ∈ Q i, α g = e * g * e⁻¹) ∧
      (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
        LieModel (↥(Q i) ⧸ Subgroup.center ↥(Q i)) t' n' 2 (p * f')) ∧
      ∃ t₁ ∈ Q i, α t₁ = t₁ ∧ ∃ t₂ ∈ Q i, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
        (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁

theorem LieLayerData.conclusion {G : Type} [Group G] [Finite G] {p : ℕ} {α : MulAut G}
    {X : Subgroup G} (h : LieLayerData p α X) :
    (∃ D : Subgroup G, IsComponentOf X D) ∧
      (∀ D : Subgroup G, IsComponentOf X D → (∀ g ∈ D, α g ∈ D) →
        (∀ e ∈ D, ¬ ∀ g ∈ D, α g = e * g * e⁻¹) ∧
        (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
          LieModel (↥D ⧸ Subgroup.center ↥D) t' n' 2 (p * f')) ∧
        ∃ t₁ ∈ D, α t₁ = t₁ ∧ ∃ t₂ ∈ D, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
          (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁) ∧
      ∀ g ∈ X, α g = g → (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ inSubgroup layer X := by
  obtain ⟨ι, Q, hne, hQ, hsolv, hN, hodd, hdata⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨i⟩ := hne
    exact ⟨Q i, hQ i⟩
  · intro D hD hDα
    obtain ⟨i, rfl⟩ := isComponentOf_eq_of_decomposition Q hQ hsolv hD
    exact hdata i hDα
  · intro g hg _ hk
    exact mem_inSubgroup_layer_of_odd_index Q hQ hsolv hN hodd hg hk

theorem lieGood_of_layerData {t : StatedLieTag}
    (h : ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LocalRankLeTwo p T →
      CFSG.pRank p T = 1 → ∀ n f₀ : ℕ, 1 ≤ f₀ → LieModel T t n 2 (p * f₀) →
      ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α → FixModel t n f₀ α →
      ∀ x : T, x ^ p = 1 → x ≠ 1 → α x = x → ∀ y : T, y ^ 2 = 1 → y ≠ 1 → x * y = y * x →
        LieLayerData p α (Subgroup.centralizer ({x} : Set T))) :
    LieGoodComponentFixT t := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx y hy2 hy1 hxy
  exact (h T p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx y hy2 hy1 hxy).conclusion

section Sector

open CFSG.RankThree.Chevalley (exhaustionPhi)


@[expose] def LayerSector (τ : Tag) (e : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f₀ : ℕ), p.Prime → 5 ≤ p → 1 ≤ f₀ →
    Nat.card K = 2 ^ (p * f₀) → ∀ σ : K ≃+* K, orderOf σ = p →
    (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) → CFSG.pRank p (adjointGroup τ K) = 1 →
    ∀ x : adjointGroup τ K, x ^ p = 1 → x ≠ 1 → entrywiseAdjointAut τ σ x = x →
      LieLayerData p (entrywiseAdjointAut τ σ)
        (Subgroup.centralizer ({x} : Set (adjointGroup τ K)))

end Sector

end CFSG.RankThree.PartOne.KLC
