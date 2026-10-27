module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePrimeCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicSemiregularBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeKernel

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

variable {G : Type} [Group G] [Finite G]

theorem pair_sylow_of_fixed
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {p : ℕ} (hp : p.Prime) (hpm : p ∣ Nat.card (conjugacyWithin H z))
    {x : G} (hx : orderOf x = p) {a b : rightCosetSpace H}
    (ha : rightCosetTranslate H a x = a) (hb : rightCosetTranslate H b x = b) (hab : a ≠ b) :
    ∃ S : Sylow p (Subgroup.centralizer ({x} : Set G)),
      pointFixedSet H ((S : Subgroup (Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype) = {a, b} := by
  obtain ⟨hdt, hsyl⟩ :=
    minimalLocalFailure_prime_centralizer_sylow_fixed_points h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨g, hgα, hgβ⟩ := hdt (rightCosetMk H 1) beta a b hbeta.symm hab
  have hainv : rightCosetTranslate H a g⁻¹ = rightCosetMk H 1 := by
    rw [← hgα, rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  have hbinv : rightCosetTranslate H b g⁻¹ = beta := by
    rw [← hgβ, rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  let x' := g * x * g⁻¹
  have hx'B : x' ∈ pairPointStabilizer H beta := by
    refine ⟨(mem_rightCosetStabilizer_iff H _ _).mpr ?_,
      (mem_rightCosetStabilizer_iff H _ _).mpr ?_⟩
    · change rightCosetTranslate H (rightCosetMk H 1) (g * x * g⁻¹) = rightCosetMk H 1
      rw [translate_conj, hgα, ha, hainv]
    · change rightCosetTranslate H beta (g * x * g⁻¹) = beta
      rw [translate_conj, hgβ, hb, hbinv]
  have hx' : orderOf x' = p := by
    have hconj := orderOf_conj_eq x g⁻¹
    rw [inv_inv, hx] at hconj
    exact hconj
  let : Fact p.Prime := ⟨hp⟩
  let C := Subgroup.centralizer ({x} : Set G)
  let C' := Subgroup.centralizer ({x'} : Set G)
  let P₀ : Sylow p (pairPointStabilizer H beta ⊓ C' : Subgroup G) := default
  obtain ⟨⟨S', hS'⟩, hfix₀⟩ := hsyl p hp hpm x' hx'B hx' P₀
  let P₀' := (P₀ : Subgroup (pairPointStabilizer H beta ⊓ C' : Subgroup G)).map
    (pairPointStabilizer H beta ⊓ C').subtype
  let P := P₀'.map (MulAut.conj g⁻¹).toMonoidHom
  have hCx : C = C'.map (MulAut.conj g⁻¹).toMonoidHom := by
    have hc := centralizer_conj_eq_map x' g⁻¹
    have hx'x : g⁻¹ * x' * g⁻¹⁻¹ = x := by
      change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group
    rwa [hx'x] at hc
  have hPC : P ≤ C := by
    rw [hCx]
    exact Subgroup.map_mono ((Subgroup.map_subtype_le _).trans inf_le_right)
  have hP₀'S : P₀' = (S' : Subgroup C').map C'.subtype := hS'.symm
  have hcard : Nat.card P = p ^ (Nat.card C).factorization p := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP₀'S, card_sylow_map, hCx,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  obtain ⟨S, hS⟩ := exists_sylow_map_eq_of_card hPC hcard
  refine ⟨S, ?_⟩
  rw [hS]
  ext ω
  rw [mem_pointFixedSet_map_conj]
  rw [hfix₀]
  constructor
  · rintro (h1 | h1)
    · left
      rw [← hgα, ← h1, rightCosetTranslate_mul, inv_mul_cancel, rightCosetTranslate_one]
    · right
      rw [Set.mem_singleton_iff] at h1 ⊢
      rw [← hgβ, ← h1, rightCosetTranslate_mul, inv_mul_cancel, rightCosetTranslate_one]
  · rintro (h1 | h1)
    · left
      rw [h1, hainv]
    · right
      rw [Set.mem_singleton_iff] at h1 ⊢
      rw [h1, hbinv]

theorem centralizer_unordered_pair_transitive
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {p : ℕ} (hp : p.Prime) (hpm : p ∣ Nat.card (conjugacyWithin H z))
    {x : G} (hx : orderOf x = p) :
    let Δ := pointFixedSet H (Subgroup.zpowers x)
    ∀ a ∈ Δ, ∀ b ∈ Δ, ∀ c ∈ Δ, ∀ d ∈ Δ, a ≠ b → c ≠ d →
      ∃ g ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G),
        (pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d) ∨
          (pointRightCosetMul H a g = d ∧ pointRightCosetMul H b g = c) := by
  intro Δ a ha b hb c hc d hd hab hcd
  have hfixΔ : ∀ ω ∈ Δ, rightCosetTranslate H ω x = ω := by
    intro ω hω
    have hω' : ω ∈ pointFixedSet H (Subgroup.zpowers x) := hω
    rw [← fixed_set_eq_pointFixedSet_zpowers] at hω'
    exact hω'
  obtain ⟨S₁, hS₁⟩ := pair_sylow_of_fixed h hcomm hsmallerR1 hbeta ht hproper hp hpm hx
    (hfixΔ a ha) (hfixΔ b hb) hab
  obtain ⟨S₂, hS₂⟩ := pair_sylow_of_fixed h hcomm hsmallerR1 hbeta ht hproper hp hpm hx
    (hfixΔ c hc) (hfixΔ d hd) hcd
  let : Fact p.Prime := ⟨hp⟩
  let C := Subgroup.centralizer ({x} : Set G)
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq C S₁ S₂
  have hmap := sylow_ambient_image_smul p C S₁ k
  rw [hk] at hmap
  have hmemS₂ : ∀ ω, ω ∈ pointFixedSet H ((S₂ : Subgroup C).map C.subtype) ↔
      rightCosetTranslate H ω (k : G) = a ∨ rightCosetTranslate H ω (k : G) = b := by
    intro ω
    rw [hmap, mem_pointFixedSet_map_conj, hS₁]
    rfl
  have hback : ∀ ω, rightCosetTranslate H (rightCosetTranslate H ω (k : G)⁻¹) (k : G) = ω := by
    intro ω
    rw [rightCosetTranslate_mul, inv_mul_cancel, rightCosetTranslate_one]
  have haS₂ : rightCosetTranslate H a (k : G)⁻¹ ∈ ({c, d} : Set (rightCosetSpace H)) := by
    rw [← hS₂, hmemS₂, hback]
    exact Or.inl rfl
  have hbS₂ : rightCosetTranslate H b (k : G)⁻¹ ∈ ({c, d} : Set (rightCosetSpace H)) := by
    rw [← hS₂, hmemS₂, hback]
    exact Or.inr rfl
  have hne : rightCosetTranslate H a (k : G)⁻¹ ≠ rightCosetTranslate H b (k : G)⁻¹ := by
    intro heq
    apply hab
    have h1 := congrArg (fun ω => rightCosetTranslate H ω (k : G)) heq
    simp only [hback] at h1
    exact h1
  refine ⟨(k : G)⁻¹, mem_centralizer_zpowers_of_commute (C.inv_mem k.2), ?_⟩
  rw [pointRightCosetMul_eq_translate, pointRightCosetMul_eq_translate]
  rcases haS₂ with h1 | h1 <;> rcases hbS₂ with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · rw [Set.mem_singleton_iff] at h1 h2
    exact absurd (h1.trans h2.symm) hne

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
