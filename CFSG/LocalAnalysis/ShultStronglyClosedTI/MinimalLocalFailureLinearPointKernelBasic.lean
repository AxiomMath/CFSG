module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureChainInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairPointNormalizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped LinearAlgebra.Projectivization

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pair_stabilizer_relIndex_eq {H : Subgroup G} {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1)
    (htwo : ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d) :
    (pairPointStabilizer H beta).relIndex H = Nat.card (rightCosetSpace H) - 1 := by
  let : MulAction H (rightCosetSpace H) :=
    { smul := fun l omega => rightCosetTranslate H omega (l : G)⁻¹
      one_smul := fun omega => by
        change rightCosetTranslate H omega ((1 : H) : G)⁻¹ = omega
        rw [Subgroup.coe_one, inv_one, rightCosetTranslate_one]
      mul_smul := fun l k omega => by
        change rightCosetTranslate H omega ((l * k : H) : G)⁻¹ =
          rightCosetTranslate H (rightCosetTranslate H omega (k : G)⁻¹) (l : G)⁻¹
        rw [rightCosetTranslate_mul, Subgroup.coe_mul, mul_inv_rev] }
  have hsmul : ∀ (l : H) (omega : rightCosetSpace H),
      l • omega = rightCosetTranslate H omega (l : G)⁻¹ := fun _ _ => rfl
  have hinv : ∀ (g : G) (omega : rightCosetSpace H),
      rightCosetTranslate H omega g⁻¹ = omega ↔ rightCosetTranslate H omega g = omega := by
    intro g omega
    constructor
    · intro hg
      calc rightCosetTranslate H omega g = rightCosetTranslate H
            (rightCosetTranslate H omega g⁻¹) g := by rw [hg]
        _ = omega := by rw [rightCosetTranslate_mul, inv_mul_cancel, rightCosetTranslate_one]
    · intro hg
      calc rightCosetTranslate H omega g⁻¹ = rightCosetTranslate H
            (rightCosetTranslate H omega g) g⁻¹ := by rw [hg]
        _ = omega := by rw [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  have hstab : MulAction.stabilizer H beta = (pairPointStabilizer H beta).subgroupOf H := by
    ext l
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, hinv]
    change _ ↔ (l : G) ∈ rightCosetStabilizer H (rightCosetMk H 1) ⊓
      rightCosetStabilizer H beta
    rw [rightCosetStabilizer_base, Subgroup.mem_inf, mem_rightCosetStabilizer_iff]
    exact ⟨fun h => ⟨l.2, h⟩, fun h => h.2⟩
  have horbit : MulAction.orbit H beta = {omega | omega ≠ rightCosetMk H 1} := by
    ext omega
    constructor
    · rintro ⟨l, rfl⟩ hl
      apply hbeta
      have h1 : rightCosetTranslate H (rightCosetMk H 1) (l : G) = rightCosetMk H 1 :=
        (translate_base_iff H _).mpr l.2
      change l • beta = rightCosetMk H 1 at hl
      rw [hsmul] at hl
      have h2 : beta = rightCosetTranslate H (rightCosetMk H 1) (l : G) := by
        rw [← hl, rightCosetTranslate_mul, inv_mul_cancel, rightCosetTranslate_one]
      rw [h2]
      exact h1
    · intro homega
      obtain ⟨g, hgα, hgβ⟩ := htwo (rightCosetMk H 1) beta (rightCosetMk H 1) omega
        hbeta.symm (Ne.symm homega)
      have hgH : g ∈ H := (translate_base_iff H g).mp hgα
      refine ⟨⟨g⁻¹, H.inv_mem hgH⟩, ?_⟩
      change (⟨g⁻¹, H.inv_mem hgH⟩ : H) • beta = omega
      rw [hsmul, Subgroup.coe_mk, inv_inv, hgβ]
  have hcard : {omega : rightCosetSpace H | omega ≠ rightCosetMk H 1}.ncard =
      Nat.card (rightCosetSpace H) - 1 := by
    have hset : {omega : rightCosetSpace H | omega ≠ rightCosetMk H 1} =
        Set.univ \ {rightCosetMk H 1} := by
      ext omega
      simp
    rw [hset, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, horbit, hcard]

theorem proper_pair_aligned_linear
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k)) :
    let K := minimalLocalFailureProperPairHull H z beta t
    ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      ∃ ψ : K ≃* PSL2MatrixGroup k,
        (H.subgroupOf K).map ψ.toMonoidHom = CFSG.GorensteinWalter.psl2Borel k ∧
        ∃ f : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} ≃ ℙ k (Fin 2 → k),
          ∀ (x : K) (ω ω' : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
            (ω' : rightCosetSpace H) = rightCosetTranslate H ω x → f ω' = (ψ x)⁻¹ • f ω := by
  intro K
  obtain ⟨-, -, -, hmodel, -⟩ :=
    minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨T, -, -, -, -, -, -, -, -, -, -, hTlin, hTsuz, -⟩ :=
    minimalLocalFailure_proper_pair_hull_point_normalizer h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, hQ4, -⟩ := CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  rcases hmodel with ⟨-, -, -, -, k, _, _, hk, ψ, hψ₀, -, -, f, -, hf, -⟩ |
    ⟨m, -, hQm, -, k, _, _, hk, ψ, -⟩
  · exact ⟨k, inferInstance, inferInstance, hk, ψ, hψ₀, f, hf⟩
  · exfalso
    have h1 := (hTlin hlin).1
    have h2 := (hTsuz ⟨m, k, inferInstance, inferInstance, hk, hk.trans hQm.symm, ⟨ψ⟩⟩).1
    have hQ4' : 4 ≤ Nat.card (minimalLocalFailurePairActionPointHull H z) := hQ4
    rw [h1] at h2
    nlinarith

theorem proper_pair_hull_faithful_on_orbit
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k))
    {x : G} (hxK : x ∈ minimalLocalFailureProperPairHull H z beta t)
    (hfix : ∀ y ∈ minimalLocalFailureProperPairHull H z beta t,
      rightCosetTranslate H (rightCosetMk H y) x = rightCosetMk H y) : x = 1 := by
  obtain ⟨k, _, _, -, ψ, -, f, hf⟩ :=
    proper_pair_aligned_linear h hcomm hsmallerR1 hbeta ht hproper hlin
  have htriv : ∀ p : ℙ k (Fin 2 → k), (ψ ⟨x, hxK⟩)⁻¹ • p = p := by
    intro p
    obtain ⟨ω, rfl⟩ := f.surjective p
    obtain ⟨y, hyK, hy⟩ := ω.2
    have hω : rightCosetTranslate H (ω : rightCosetSpace H)
        (⟨x, hxK⟩ : minimalLocalFailureProperPairHull H z beta t) =
        (ω : rightCosetSpace H) := by
      rw [← hy]
      exact hfix y hyK
    exact (hf ⟨x, hxK⟩ ω ω hω.symm).symm
  have hψ : (ψ ⟨x, hxK⟩)⁻¹ = 1 := eq_of_smul_eq_smul (α := ℙ k (Fin 2 → k)) fun p => by
    rw [htriv p, one_smul]
  have hx : (⟨x, hxK⟩ : minimalLocalFailureProperPairHull H z beta t) = 1 := by
    rw [inv_eq_one, MulEquiv.map_eq_one_iff] at hψ
    exact hψ
  exact congrArg Subtype.val hx

theorem point_normalizer_eq_root_sup
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k)) :
    let B := pairPointStabilizer H beta
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    Subgroup.normalizer (K : Set G) ⊓ H = Q ⊔ B ∧ Q ⊓ B = ⊥ ∧
      (∀ ω ∈ baseOrbit H K, ∀ ω' ∈ baseOrbit H K, ω ≠ rightCosetMk H 1 →
        ω' ≠ rightCosetMk H 1 → ∃! s : Q, rightCosetTranslate H ω (s : G) = ω') := by
  intro B K Q
  obtain ⟨T, hTM, hTp, hall, -, -, -, -, hNeq, hTB, -, hTlin, -, hregT⟩ :=
    minimalLocalFailure_proper_pair_hull_point_normalizer h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨hQH, hQK, -, -, hQp, -, -⟩ :=
    CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  let M := H ⊓ K
  have hQM : Q ≤ M := le_inf hQH hQK
  have hQT : Q ≤ T := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQp' : IsPGroup 2 (Q.subgroupOf M) :=
      hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
    obtain ⟨S, hS⟩ := hQp'.exists_le_sylow
    rw [← hall S]
    intro x hx
    exact ⟨⟨x, hQM hx⟩, hS hx, rfl⟩
  have hTQ : T = Q := by
    refine (Subgroup.eq_of_le_of_card_ge hQT ?_).symm
    rw [(hTlin hlin).1]
  rw [hTQ] at hNeq hTB hregT
  exact ⟨hNeq, hTB, hregT⟩

end CFSG.ShultStronglyClosedTI.LinearChain
