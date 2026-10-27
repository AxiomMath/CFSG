module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerCore
public import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd

public section

namespace CFSG.RankThree.PartOne.KCSpFull

open CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation)
open CFSG.ComponentClassification

variable {r : ℕ} {K : Type} [Field K]

theorem conj_proj_eq_conjAut (g : StatedSp r K) :
    MulAut.conj (proj r K g) = conjAut r K ⟨(g : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp g.2⟩ := by
  refine MulEquiv.ext fun t => ?_
  obtain ⟨y, rfl⟩ := SymplecticHigher.proj_surjective (r := r) (K := K) t
  rw [MulAut.conj_apply]
  change _ = proj r K (conjSp r K _ y)
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem exists_semilinear_of_inner {α : MulAut (StatedProj (StatedSp r K))}
    (h : α ∈ OuterAutomorphisms.inner (StatedProj (StatedSp r K))) :
    ∃ (A : gsp r K) (σ : K ≃+* K), α = conjAut r K A * fieldAut r K σ := by
  obtain ⟨t, rfl⟩ := h
  obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective (r := r) (K := K) t
  refine ⟨⟨(g : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp g.2⟩, RingEquiv.refl K, ?_⟩
  have h1 : fieldAut r K (RingEquiv.refl K) = 1 := map_one (fieldAut r K)
  rw [h1, mul_one]
  exact conj_proj_eq_conjAut g

variable {ℓ f p : ℕ} {Ahat : Subgroup (StatedSp r K)}

theorem SpPlaneSetup.exists_semilinear_of_ne_exceptional (S : SpPlaneSetup ℓ f p r K Ahat)
    (hne : ¬ (ℓ = 2 ∧ r = 2)) (α : MulAut (StatedProj (StatedSp r K))) :
    ∃ (A : gsp r K) (σ : K ≃+* K), α = conjAut r K A * fieldAut r K σ := by
  have := S.finite
  have := S.charP
  by_cases hr3 : 3 ≤ r
  · exact (automorphism_generation (K := K) hr3).2 α
  · have hℓ2 : ℓ ≠ 2 := fun h => hne ⟨h, by have := S.two_le_r; omega⟩
    have hodd : ringChar K ≠ 2 := by
      rw [ringChar.eq K ℓ]
      exact hℓ2
    exact (odd_symplectic_automorphism_semilinear_representation hodd S.two_le_r).1 α

theorem SpPlaneSetup.inner_of_rank_two_even {Ahat₂ : Subgroup (StatedSp 2 K)}
    (S : SpPlaneSetup ℓ f p 2 K Ahat₂) (hℓ : ℓ = 2)
    {α : MulAut (StatedProj (StatedSp 2 K))}
    (hcent : ∀ x ∈ Ahat₂, x ≠ 1 → CentralizesListed α x) :
    α ∈ OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) := by
  have := S.finite
  have D := S.decomp
  obtain ⟨M₁, M₂, hM₁, hM₂, hne, hV₁, hV₂⟩ := D.two_active
  obtain ⟨t₁, ht₁, ht₁1⟩ := S.exists_ne_one_mem hM₁
  have ht₁1' : (t₁ : StatedSp 2 K) ≠ 1 := fun h => ht₁1 (Subtype.ext h)
  obtain ⟨hlisted, h2dim, -⟩ := S.spFixedListed D hM₁ hV₁ t₁.2 ht₁ ht₁1'
  have hdim := spFixedDim_eq_finrank_ker (t₁ : StatedSp 2 K)
  obtain ⟨u, hu, hu0⟩ : ∃ u ∈ LinearMap.ker (spEnd (t₁ : StatedSp 2 K) - 1), u ≠ 0 := by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro h
    have h0 : Module.finrank K (LinearMap.ker (spEnd (t₁ : StatedSp 2 K) - 1)) = 0 := by
      rw [h]
      exact finrank_bot K _
    omega
  have hq : Nat.card K ≠ 2 := by
    intro h
    exact S.not_exceptional ⟨rfl, by rw [← S.card_K, h]⟩
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf1 : f = 1 := by have := S.one_le_f; omega
    subst hf1
    apply hq
    rw [S.card_K, hℓ, pow_one]
  have hK : Nat.card K = 2 ^ f := by rw [S.card_K, hℓ]
  have himg : spFixedLayerImage (t₁ : StatedSp 2 K) =
      (spFixedFactor (t₁ : StatedSp 2 K)).map (proj 2 K) := by
    have h42 : ¬ (spFixedDim (t₁ : StatedSp 2 K) = 4 ∧ Nat.card K = 2) := fun h => hq h.2
    simp [spFixedLayerImage, hlisted, h42]
  have hα' : ∀ t : K, α (proj 2 K (spTransvection u t)) = proj 2 K (spTransvection u t) := by
    intro t
    have hmem : spTransvection u t ∈ spFixedFactor (t₁ : StatedSp 2 K) :=
      spTransvection_mem_spFixedFactor (mem_ker_sub_one_iff.mp hu) t
    have h1 := (hcent _ t₁.2 ht₁1').1 hlisted _ (himg ▸ Subgroup.mem_map_of_mem _ hmem)
    exact (commute_conj_iff S.conj_injective α _).mp h1
  exact even_symplectic_rank_two_inner_of_fixes_transvections hf2 hK u hu0 α hα'

theorem SpPlaneSetup.exists_semilinear_of_centralizes (S : SpPlaneSetup ℓ f p r K Ahat)
    {α : MulAut (StatedProj (StatedSp r K))}
    (hcent : ∀ x ∈ Ahat, x ≠ 1 → CentralizesListed α x) :
    ∃ (A : gsp r K) (σ : K ≃+* K), α = conjAut r K A * fieldAut r K σ := by
  by_cases hne : ℓ = 2 ∧ r = 2
  · obtain ⟨hℓ, hr⟩ := hne
    subst hr
    exact exists_semilinear_of_inner (S.inner_of_rank_two_even hℓ hcent)
  · exact S.exists_semilinear_of_ne_exceptional hne α

theorem SpPlaneSetup.eq_one_of_centralizes (S : SpPlaneSetup ℓ f p r K Ahat)
    {α : MulAut (StatedProj (StatedSp r K))}
    (hcent : ∀ x ∈ Ahat, x ≠ 1 → CentralizesListed α x) : α = 1 := by
  have := S.neZero
  obtain ⟨A, σ, hα⟩ := S.exists_semilinear_of_centralizes hcent
  exact S.rigidity_of_semilinear A σ hα hcent

end CFSG.RankThree.PartOne.KCSpFull
