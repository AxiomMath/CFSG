module

public import CFSG.LocalAnalysis.UniqueFourCatalog.Glue
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureSymplectic
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.ClassicalGroups.Symplectic.Model

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open Subgroup CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)
open CFSG.LocalAnalysis.RankThreeUC (twoLocalClosure)

@[expose] def ClosureTop (G : Type) [Group G] : Prop :=
  ∀ E S₀ : Subgroup G, Odd (Nat.card E) → S₀ ≠ ⊥ → IsPGroup 2 S₀ →
    E ≤ normalizer (S₀ : Set G) → twoLocalClosure E = ⊤

theorem odd_card_of_isElemAbelian {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElemAbelian p E) : Odd (Nat.card E) := by
  have hEp : IsPGroup p E := fun x => ⟨1, by
    have := hE.2 x x.2
    apply Subtype.ext
    simpa using this⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEp
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

theorem not_uniqueFour_of_closureTop {G : Type} [Group G] [Finite G] (hS : Standing4 G)
    (h : ClosureTop G) : ¬ uniqueFourUnique G :=
  not_uniqueFour_of_closure hS (fun _ hp hp2 E S₀ hE hS₀ hS₀2 hEN =>
    h E S₀ (odd_card_of_isElemAbelian hp hp2 hE) hS₀ hS₀2 hEN)

theorem closureTop_of_lift {G A : Type} [Group G] [Group A] [Finite A]
    (φ : A →* G) (hφ : Function.Surjective φ)
    (hc : φ.ker ≤ Subgroup.center A) (hker : ∀ z ∈ φ.ker, z ^ 2 = 1 → z = 1)
    (h : ClosureTop A) : ClosureTop G := by
  intro E S₀ hE hS₀ hS₀2 hEN
  obtain ⟨P, hP, hP2, hEP⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_normalized_two_subgroup φ hφ hc hS₀ hS₀2 hEN
  have hcl := h (E.comap φ) P
    (CFSG.LocalAnalysis.RankThreeUC.odd_card_comap φ hker hE) hP hP2 hEP
  have hle := CFSG.LocalAnalysis.RankThreeUC.map_twoLocalClosure_le_of_ker φ hker (E.comap φ)
  rw [hcl, Subgroup.map_top, MonoidHom.range_eq_top.2 hφ,
    Subgroup.map_comap_eq_self_of_surjective hφ] at hle
  exact top_le_iff.mp hle

theorem closureTop_of_lift_gen {G A : Type} [Group G] [IsSimpleGroup G] [Group A] [Finite A]
    (φ : A →* G) (hφ : Function.Surjective φ)
    (hc : φ.ker ≤ Subgroup.center A) (hker : ∀ z ∈ φ.ker, z ^ 2 = 1 → z = 1)
    (𝒯 : Set A) (hconj : ∀ g t, t ∈ 𝒯 → g * t * g⁻¹ ∈ 𝒯) (hnt : ∃ t ∈ 𝒯, φ t ≠ 1)
    (h : ∀ E P : Subgroup A, Odd (Nat.card E) → P ≠ ⊥ → IsPGroup 2 P →
      E ≤ normalizer (P : Set A) → 𝒯 ⊆ (twoLocalClosure E : Set A)) : ClosureTop G := by
  intro E S₀ hE hS₀ hS₀2 hEN
  obtain ⟨P, hP, hP2, hEP⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_normalized_two_subgroup φ hφ hc hS₀ hS₀2 hEN
  have hT := h (E.comap φ) P
    (CFSG.LocalAnalysis.RankThreeUC.odd_card_comap φ hker hE) hP hP2 hEP
  have hle := CFSG.LocalAnalysis.RankThreeUC.map_twoLocalClosure_le_of_ker φ hker (E.comap φ)
  rw [Subgroup.map_comap_eq_self_of_surjective hφ] at hle
  obtain ⟨t, ht, ht1⟩ := hnt
  set N := Subgroup.normalClosure (φ '' 𝒯) with hN
  have hNne : N ≠ ⊥ := by
    intro hbot
    have : φ t ∈ N := Subgroup.subset_normalClosure ⟨t, ht, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact ht1 this
  have hNtop : N = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_left hNne
  have hNle : N ≤ twoLocalClosure E := by
    rw [hN, Subgroup.normalClosure, Subgroup.closure_le]
    intro g hg
    rw [Group.mem_conjugatesOfSet_iff] at hg
    obtain ⟨b, ⟨t', ht', rfl⟩, hbg⟩ := hg
    rw [isConj_iff] at hbg
    obtain ⟨d, rfl⟩ := hbg
    obtain ⟨a, rfl⟩ := hφ d
    have : φ a * φ t' * (φ a)⁻¹ = φ (a * t' * a⁻¹) := by simp [map_mul, map_inv]
    rw [this]
    exact hle ⟨a * t' * a⁻¹, hT (hconj a t' ht'), rfl⟩
  exact top_le_iff.mp (hNtop ▸ hNle)

theorem closureTop_of_proj {G : Type} [Group G]
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [CharP K 2]
    (A : Subgroup (GL ι K)) [Finite A] (e : G ≃* StatedProj A) (h : ClosureTop A) :
    ClosureTop G := by
  let φ : A →* G := e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf A))
  have hφ : Function.Surjective φ := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = (StatedScalars ι K).subgroupOf A := by
    ext z
    rw [MonoidHom.mem_ker]
    show e.symm (QuotientGroup.mk z) = 1 ↔ _
    rw [map_eq_one_iff _ e.symm.injective, QuotientGroup.eq_one_iff]
  exact closureTop_of_lift φ hφ
    (hker ▸ CFSG.LocalAnalysis.RankThreeUC.statedScalars_subgroupOf_le_center A)
    (fun z hz h2 => CFSG.LocalAnalysis.RankThreeUC.eq_one_of_sq_eq_one_of_mem_statedScalars
      A (hker ▸ hz) h2) h

theorem closureTop_of_proj_gen {G : Type} [Group G] [IsSimpleGroup G]
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [CharP K 2]
    (A : Subgroup (GL ι K)) [Finite A] (e : G ≃* StatedProj A) (𝒯 : Set A)
    (hconj : ∀ g t, t ∈ 𝒯 → g * t * g⁻¹ ∈ 𝒯)
    (hnt : ∃ t ∈ 𝒯, t ∉ (StatedScalars ι K).subgroupOf A)
    (h : ∀ E P : Subgroup A, Odd (Nat.card E) → P ≠ ⊥ → IsPGroup 2 P →
      E ≤ normalizer (P : Set A) → 𝒯 ⊆ (twoLocalClosure E : Set A)) : ClosureTop G := by
  let φ : A →* G := e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf A))
  have hφ : Function.Surjective φ := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = (StatedScalars ι K).subgroupOf A := by
    ext z
    rw [MonoidHom.mem_ker]
    show e.symm (QuotientGroup.mk z) = 1 ↔ _
    rw [map_eq_one_iff _ e.symm.injective, QuotientGroup.eq_one_iff]
  obtain ⟨t, ht, htn⟩ := hnt
  exact closureTop_of_lift_gen φ hφ
    (hker ▸ CFSG.LocalAnalysis.RankThreeUC.statedScalars_subgroupOf_le_center A)
    (fun z hz h2 => CFSG.LocalAnalysis.RankThreeUC.eq_one_of_sq_eq_one_of_mem_statedScalars
      A (hker ▸ hz) h2) 𝒯 hconj
    ⟨t, ht, fun h1 => htn (hker ▸ h1)⟩ h

end CFSG.LocalAnalysis.UniqueFourCatalog
