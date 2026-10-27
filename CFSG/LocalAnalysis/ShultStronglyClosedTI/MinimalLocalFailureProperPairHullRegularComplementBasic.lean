module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureChainInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairInvolutionsCentralize

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type} [Group G] [Finite G]

theorem pairInvolutionCentralizesConclusion
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      PairInvolutionCentralizesConclusion H z beta t u :=
  PairInvolutionsCentralize.minimalLocalFailure_pair_involutions_centralize_point_group h hcomm
    hsmallerR1 hbeta ht hproper

omit [Finite G] in
theorem card_baseOrbit_mul (H K : Subgroup G) :
    Nat.card (baseOrbit H K) * Nat.card (H ⊓ K : Subgroup G) = Nat.card K := by
  have hset : baseOrbit H K = {omega : rightCosetSpace H |
      ∃ y ∈ K, rightCosetTranslate H (rightCosetMk H 1) y = omega} := by
    ext ω
    simp only [baseOrbit, Set.mem_ofPred_eq, rightCosetTranslate_mk, one_mul]
  rw [hset]
  exact MixedClass.card_base_orbit_mul H K

omit [Finite G] in
theorem card_eq_mul_of_semidirect {M T X : Subgroup G} (hsup : M = T ⊔ X) (hinf : T ⊓ X = ⊥)
    (hT : (T.subgroupOf M).Normal) : Nat.card M = Nat.card T * Nat.card X := by
  have hTM : T ≤ M := hsup ▸ le_sup_left
  have hXM : X ≤ M := hsup ▸ le_sup_right
  have htop : T.subgroupOf M ⊔ X.subgroupOf M = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hTM, inf_eq_left.mpr hXM, ← hsup, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hcompl : (T.subgroupOf M).IsComplement' (X.subgroupOf M) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [Subgroup.disjoint_def]
      intro x hxT hxX
      have hx : (x : G) ∈ T ⊓ X := ⟨hxT, hxX⟩
      rw [hinf] at hx
      exact Subtype.ext hx
    · rw [← Subgroup.normal_mul, htop, Subgroup.coe_top]
  rw [← hcompl.card_mul_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv]

omit [Finite G] in
theorem exists_injective_hom_of_regular (H K C : Subgroup G) (Γ : Set (rightCosetSpace H))
    (hΓ : Γ.Nonempty)
    (hreg : ∀ ω ∈ Γ, ∀ ω' ∈ Γ, ∃! x : K, rightCosetTranslate H ω x = ω')
    (hCK : ∀ c ∈ C, ∀ x ∈ K, c * x = x * c)
    (hCΓ : ∀ c ∈ C, ∀ ω ∈ Γ, rightCosetTranslate H ω c ∈ Γ)
    (hfaith : ∀ c ∈ C, (∀ ω ∈ Γ, rightCosetTranslate H ω c = ω) → c = 1) :
    ∃ f : C →* K, Function.Injective f := by
  obtain ⟨γ₀, hγ₀⟩ := hΓ
  have hex : ∀ c : C, ∃! x : K, rightCosetTranslate H γ₀ x = rightCosetTranslate H γ₀ c :=
    fun c => hreg γ₀ hγ₀ _ (hCΓ c c.2 γ₀ hγ₀)
  let k : C → K := fun c => (hex c).exists.choose
  have hk : ∀ c : C, rightCosetTranslate H γ₀ (k c) = rightCosetTranslate H γ₀ c :=
    fun c => (hex c).exists.choose_spec
  have hkuniq : ∀ (c : C) (x : K), rightCosetTranslate H γ₀ x = rightCosetTranslate H γ₀ c →
      x = k c := fun c x hx => (hex c).unique hx (hk c)
  have hkmul : ∀ c d : C, k (c * d) = k d * k c := by
    intro c d
    symm
    apply hkuniq
    calc rightCosetTranslate H γ₀ ((k d * k c : K) : G)
        = rightCosetTranslate H (rightCosetTranslate H γ₀ (k d)) (k c) := by
          rw [rightCosetTranslate_mul]
          rfl
      _ = rightCosetTranslate H (rightCosetTranslate H γ₀ d) (k c) := by rw [hk d]
      _ = rightCosetTranslate H γ₀ ((d : G) * k c) := by rw [rightCosetTranslate_mul]
      _ = rightCosetTranslate H γ₀ ((k c : G) * d) := by rw [hCK d d.2 (k c) (k c).2]
      _ = rightCosetTranslate H (rightCosetTranslate H γ₀ (k c)) d := by
          rw [rightCosetTranslate_mul]
      _ = rightCosetTranslate H (rightCosetTranslate H γ₀ c) d := by rw [hk c]
      _ = rightCosetTranslate H γ₀ ((c * d : C) : G) := by
          rw [rightCosetTranslate_mul]
          rfl
  let f : C →* K := MonoidHom.mk' (fun c => (k c)⁻¹) (fun c d => by rw [hkmul, mul_inv_rev])
  refine ⟨f, (injective_iff_map_eq_one f).mpr fun c hc => ?_⟩
  have hkc : k c = 1 := inv_eq_one.mp hc
  have hfix0 : rightCosetTranslate H γ₀ c = γ₀ := by
    rw [← hk c, hkc, OneMemClass.coe_one, rightCosetTranslate_one]
  apply Subtype.ext
  apply hfaith c c.2
  intro ω hω
  obtain ⟨x, hx, -⟩ := hreg γ₀ hγ₀ ω hω
  rw [← hx, rightCosetTranslate_mul, ← hCK c c.2 x x.2, ← rightCosetTranslate_mul, hfix0]

end CFSG.ShultStronglyClosedTI.ProperPairModel
