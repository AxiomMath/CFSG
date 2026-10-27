module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairLinearOrSuzukiModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedPointModelHypotheses
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedField
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.CyclicPair
open scoped LinearAlgebra.Projectivization

variable {G : Type} [Group G] [Finite G]

theorem proper_pair_point_involutions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    {x : G | x ∈ H ⊓ minimalLocalFailureProperPairHull H z beta t ∧ orderOf x = 2} =
      (minimalLocalFailurePairActionPointHull H z : Set G) \ {1} := by
  obtain ⟨h1, h2, h3⟩ := proper_pair_point_root_classes h hcomm hbeta ht hproper
  rw [← h3, ← h2, h1]

theorem card_involutions_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (M : Subgroup A) :
    Nat.card {y : B // y ∈ M.map e.toMonoidHom ∧ orderOf y = 2} =
      Nat.card {x : A // x ∈ M ∧ orderOf x = 2} := by
  refine Nat.card_congr ⟨fun y => ⟨e.symm y, ?_, ?_⟩, fun x => ⟨e x, ?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2.1
    rw [← hxy]
    simpa using hx
  · rw [MulEquiv.orderOf_eq]
    exact y.2.2
  · exact Subgroup.mem_map_of_mem _ x.2.1
  · rw [MulEquiv.orderOf_eq]
    exact x.2.2
  · intro y
    exact Subtype.ext (by simp)
  · intro x
    exact Subtype.ext (by simp)

theorem proper_pair_card_point_involutions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let K := minimalLocalFailureProperPairHull H z beta t
    Nat.card {x : K // x ∈ H.subgroupOf K ∧ orderOf x = 2} =
      Nat.card (minimalLocalFailurePairActionPointHull H z) - 1 := by
  intro K
  have hset := proper_pair_point_involutions h hcomm hbeta ht hproper
  have hQ1 : (1 : G) ∈ minimalLocalFailurePairActionPointHull H z := Subgroup.one_mem _
  have hcardQ : Nat.card ((minimalLocalFailurePairActionPointHull H z : Set G) \ {1} : Set G) =
      Nat.card (minimalLocalFailurePairActionPointHull H z) - 1 :=
    PairInvolutionFixedField.card_diff_one _
  rw [← hcardQ, ← hset]
  refine Nat.card_congr ⟨fun x => ⟨(x : G), ⟨x.2.1, x.1.2⟩, by
      rw [Subgroup.orderOf_coe]; exact x.2.2⟩,
    fun y => ⟨⟨y, y.2.1.2⟩, y.2.1.1, by
      rw [← Subgroup.orderOf_coe]; exact y.2.2⟩, fun x => rfl, fun y => rfl⟩

omit [Finite G] in
theorem pair_stabilizer_subgroupOf_eq (H K : Subgroup G) {z : G} {beta : rightCosetSpace H}
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    (pairPointStabilizer H beta).subgroupOf K =
      H.subgroupOf K ⊓ (rightConjugate H t).subgroupOf K := by
  have hbetaeq : beta = rightCosetMk H t := by
    rw [← ht.2, rightCosetTranslate_mk, one_mul]
  change (rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H beta).subgroupOf K = _
  rw [rightCosetStabilizer_base, hbetaeq, rightCosetStabilizer_mk]
  ext x
  rfl

theorem proper_pair_hull_inf_pair_stabilizer_eq
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {P : Type*} [Group P]
    (ψ : minimalLocalFailureProperPairHull H z beta t ≃* P) (S₁ S₂ : Subgroup P)
    (hψ₁ : (H.subgroupOf (minimalLocalFailureProperPairHull H z beta t)).map ψ.toMonoidHom = S₁)
    (hψ₂ : ((rightConjugate H t).subgroupOf
      (minimalLocalFailureProperPairHull H z beta t)).map ψ.toMonoidHom = S₂)
    (hcard : Nat.card (S₁ ⊓ S₂ : Subgroup P) =
      Nat.card (minimalLocalFailurePairActionPointHull H z) - 1) :
    minimalLocalFailureProperPairHull H z beta t ⊓ pairPointStabilizer H beta =
      rightInvolutionCommutatorSubgroup t (pairOddCore H beta) := by
  obtain ⟨-, -, -, -, hXB, -, -, hXcard, -, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, -, -, -, -, hXK, -⟩ := proper_pair_cyclic_commutator h hcomm hsmallerR1
    hbeta ht hproper
  have hmap : ((pairPointStabilizer H beta).subgroupOf
      (minimalLocalFailureProperPairHull H z beta t)).map ψ.toMonoidHom = S₁ ⊓ S₂ := by
    rw [pair_stabilizer_subgroupOf_eq _ _ ht, Subgroup.map_inf _ _ _ ψ.injective, hψ₁, hψ₂]
  have hcardKB : Nat.card (minimalLocalFailureProperPairHull H z beta t ⊓
      pairPointStabilizer H beta : Subgroup G) = Nat.card (S₁ ⊓ S₂ : Subgroup P) := by
    rw [← hmap, Subgroup.card_map_of_injective ψ.injective, ← Subgroup.inf_subgroupOf_left]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  symm
  apply Subgroup.eq_of_le_of_card_ge (le_inf hXK hXB)
  rw [hcardKB, hcard, hXcard]


theorem exists_ne_ne_of_three_le_card {Ω : Type*} [Finite Ω] (h : 3 ≤ Nat.card Ω) (a b : Ω) :
    ∃ c : Ω, c ≠ a ∧ c ≠ b := by
  by_contra hnone
  push Not at hnone
  have hsub : (Set.univ : Set Ω) ⊆ {a, b} := fun c _ => by
    by_cases hca : c = a
    · exact Or.inl hca
    · exact Or.inr (hnone c hca)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ] at hle
  have hpair : ({a, b} : Set Ω).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  omega

omit [Finite G] in
theorem aligned_flip_inv_smul (H K : Subgroup G) {t : G} (htK : t ∈ K)
    {P Ω : Type*} [Group P] [MulAction P Ω] (ψ : K ≃* P) {a₀ a₁ : Ω}
    (hψ₀ : (H.subgroupOf K).map ψ.toMonoidHom = MulAction.stabilizer P a₀)
    (hψ₁ : ((rightConjugate H t).subgroupOf K).map ψ.toMonoidHom = MulAction.stabilizer P a₁)
    (htwo : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : P, g • a = c ∧ g • b = d)
    (hthree : ∀ a b : Ω, ∃ c : Ω, c ≠ a ∧ c ≠ b) :
    (ψ ⟨t, htK⟩)⁻¹ • a₀ = a₁ := by
  have hconj := rightConjugate_subgroupOf_eq_map H K htK
  have hmapconj : ((H.subgroupOf K).map
      (MulAut.conj (⟨t, htK⟩ : K)⁻¹).toMonoidHom).map ψ.toMonoidHom =
      ((H.subgroupOf K).map ψ.toMonoidHom).map (MulAut.conj (ψ ⟨t, htK⟩)⁻¹).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [map_mul, map_inv]
  have hstab : MulAction.stabilizer P ((ψ ⟨t, htK⟩)⁻¹ • a₀) = MulAction.stabilizer P a₁ := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, ← hψ₀, ← hmapconj, ← hconj, hψ₁]
  exact eq_of_stabilizer_eq htwo hthree hstab

omit [Finite G] in
theorem aligned_orbit_equiv (H K : Subgroup G) {beta : rightCosetSpace H} {t : G}
    (hbetaeq : beta = rightCosetMk H t) (htK : t ∈ K)
    {P Ω : Type*} [Group P] [MulAction P Ω] (ψ : K ≃* P) {a₀ a₁ : Ω}
    (hψ₀ : (H.subgroupOf K).map ψ.toMonoidHom = MulAction.stabilizer P a₀)
    (hψ₁ : ((rightConjugate H t).subgroupOf K).map ψ.toMonoidHom = MulAction.stabilizer P a₁)
    (htwo : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : P, g • a = c ∧ g • b = d)
    (hthree : ∀ a b : Ω, ∃ c : Ω, c ≠ a ∧ c ≠ b) (ha : a₀ ≠ a₁) :
    ∃ f : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} ≃ Ω,
      (∀ (x : K) (ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
        (ω : rightCosetSpace H) = rightCosetMk H x → f ω = (ψ x)⁻¹ • a₀) ∧
      (∀ (x : K) (ω ω' : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
        (ω' : rightCosetSpace H) = rightCosetTranslate H ω x → f ω' = (ψ x)⁻¹ • f ω) ∧
      (∀ ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω},
        (ω : rightCosetSpace H) = rightCosetMk H 1 → f ω = a₀) ∧
      (∀ ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω},
        (ω : rightCosetSpace H) = beta → f ω = a₁) := by
  have hmem : ∀ w : K, (w : G) ∈ H ↔ ψ w ∈ MulAction.stabilizer P a₀ := fun w => by
    rw [← hψ₀, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]
  have hkey : ∀ x y : K, rightCosetMk H x = rightCosetMk H y ↔ (ψ x)⁻¹ • a₀ = (ψ y)⁻¹ • a₀ := by
    intro x y
    rw [PairInvolutionFixedField.rightCosetMk_eq_iff,
      show (y : G) * (x : G)⁻¹ = ((y * x⁻¹ : K) : G) from rfl, hmem,
      MulAction.mem_stabilizer_iff, map_mul, map_inv, mul_smul, smul_eq_iff_eq_inv_smul]
  have htrans : ∀ b : Ω, ∃ g : P, g • a₀ = b := fun b => by
    obtain ⟨c, hcb, -⟩ := hthree b b
    obtain ⟨g, hg, -⟩ := htwo a₀ a₁ b c ha (Ne.symm hcb)
    exact ⟨g, hg⟩
  let rep : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} → K :=
    fun ω => ⟨Classical.choose ω.2, (Classical.choose_spec ω.2).1⟩
  have hrep : ∀ ω, rightCosetMk H (rep ω) = ω := fun ω => (Classical.choose_spec ω.2).2
  let F : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} → Ω :=
    fun ω => (ψ (rep ω))⁻¹ • a₀
  have hF : ∀ (x : K) (ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
      (ω : rightCosetSpace H) = rightCosetMk H x → F ω = (ψ x)⁻¹ • a₀ :=
    fun x ω hω => (hkey (rep ω) x).mp ((hrep ω).trans hω)
  have hbij : Function.Bijective F := by
    constructor
    · intro ω₁ ω₂ h12
      apply Subtype.ext
      rw [← hrep ω₁, ← hrep ω₂]
      exact (hkey _ _).mpr h12
    · intro b
      obtain ⟨g, hg⟩ := htrans b
      refine ⟨⟨rightCosetMk H (ψ.symm g⁻¹ : K), (ψ.symm g⁻¹ : K), (ψ.symm g⁻¹).2, rfl⟩, ?_⟩
      rw [hF (ψ.symm g⁻¹) _ rfl, MulEquiv.apply_symm_apply, inv_inv, hg]
  refine ⟨Equiv.ofBijective F hbij, hF, ?_, ?_, ?_⟩
  · intro x ω ω' hω'
    obtain ⟨x₁, hx₁K, hx₁⟩ := ω.2
    have h1 : (ω' : rightCosetSpace H) = rightCosetMk H ((⟨x₁, hx₁K⟩ : K) * x : K) := by
      rw [hω', ← hx₁, rightCosetTranslate_mk]
      rfl
    change F ω' = (ψ x)⁻¹ • F ω
    rw [hF _ ω' h1, hF ⟨x₁, hx₁K⟩ ω hx₁.symm, map_mul, mul_inv_rev, mul_smul]
  · intro ω hω
    change F ω = a₀
    rw [hF 1 ω hω, map_one, inv_one, one_smul]
  · intro ω hω
    change F ω = a₁
    rw [hF ⟨t, htK⟩ ω (hω.trans hbetaeq)]
    exact aligned_flip_inv_smul H K htK ψ hψ₀ hψ₁ htwo hthree


omit [Finite G] in
theorem pair_stabilizer_subgroupOf_map (H K : Subgroup G) {z : G} {beta : rightCosetSpace H}
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) {P : Type*} [Group P] (ψ : K ≃* P) :
    ((pairPointStabilizer H beta).subgroupOf K).map ψ.toMonoidHom =
      (H.subgroupOf K).map ψ.toMonoidHom ⊓
        ((rightConjugate H t).subgroupOf K).map ψ.toMonoidHom := by
  rw [pair_stabilizer_subgroupOf_eq H K ht, Subgroup.map_inf _ _ _ ψ.injective]

omit [Finite G] in
theorem flip_coset_eq (H : Subgroup G) {z : G} {beta : rightCosetSpace H} {t : G}
    (ht : t ∈ rightPairFlipFiber H z beta) : beta = rightCosetMk H t := by
  rw [← ht.2, rightCosetTranslate_mk, one_mul]

theorem card_involutions_psl2Borel {k : Type} [Field k] [Finite k] [CharP k 2] :
    Nat.card {y : PSL2MatrixGroup k // y ∈ CFSG.GorensteinWalter.psl2Borel k ∧ orderOf y = 2} =
      Nat.card k - 1 := by
  rw [← CFSG.GorensteinWalter.psl2UpperUnipotentSubgroup_card k,
    ← PairInvolutionFixedField.card_diff_one]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  constructor
  · rintro ⟨hy, hy2⟩
    obtain ⟨hyU, hy1⟩ := (LinearModel.borel_orderOf_eq_two_iff hy).mp hy2
    exact ⟨hyU, hy1⟩
  · rintro ⟨hyU, hy1⟩
    have hyB := CFSG.GorensteinWalter.psl2UpperUnipotent_le_borel hyU
    exact ⟨hyB, (LinearModel.borel_orderOf_eq_two_iff hyB).mpr ⟨hyU, hy1⟩⟩

theorem proper_pair_linear_branch
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hO : CFSG.oddCore (minimalLocalFailureProperPairHull H z beta t) = ⊥)
    {a : ℕ} (ha : 2 ≤ a)
    (e₀ : minimalLocalFailureProperPairHull H z beta t ≃* PSL2BinaryMatrixGroup a) :
    let B := pairPointStabilizer H beta
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    Nat.card Q = 2 ^ a ∧ K ⊓ B = X ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Nat.card Q ∧
        ∃ ψ : K ≃* PSL2MatrixGroup k,
          (H.subgroupOf K).map ψ.toMonoidHom = CFSG.GorensteinWalter.psl2Borel k ∧
          ((rightConjugate H t).subgroupOf K).map ψ.toMonoidHom =
            MulAction.stabilizer (PSL2MatrixGroup k) (CFSG.GorensteinWalter.psl2ProjectiveZero k) ∧
          (B.subgroupOf K).map ψ.toMonoidHom = LinearModel.torus k ∧
          ∃ f : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} ≃
              ℙ k (Fin 2 → k),
            (∀ (x : K) (ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
              (ω : rightCosetSpace H) = rightCosetMk H x →
                f ω = (ψ x)⁻¹ • CFSG.GorensteinWalter.psl2ProjectiveInfinity k) ∧
            (∀ (x : K) (ω ω' : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
              (ω' : rightCosetSpace H) = rightCosetTranslate H ω x → f ω' = (ψ x)⁻¹ • f ω) ∧
            (∀ ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω},
              (ω : rightCosetSpace H) = rightCosetMk H 1 →
                f ω = CFSG.GorensteinWalter.psl2ProjectiveInfinity k) ∧
            (∀ ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω},
              (ω : rightCosetSpace H) = beta → f ω = CFSG.GorensteinWalter.psl2ProjectiveZero k) ∧
            Nat.card {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} =
              Nat.card Q + 1 := by
  intro B X K Q
  let k := BinaryGaloisField a
  have hcard : Nat.card k = 2 ^ a := by
    simpa [k, BinaryGaloisField] using GaloisField.card 2 a (by omega)
  let : CharP k 2 := LinearModel.charP_two_of_card hcard
  obtain ⟨ψ, hψ₀, hψ₁⟩ := proper_pair_hull_linear_aligned h hcomm hsmallerR1 hbeta ht hproper hO ha e₀
  obtain ⟨-, hQ4, -⟩ := proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  have hinv := proper_pair_card_point_involutions h hcomm hbeta ht hproper
  have hinv' := card_involutions_map_mulEquiv ψ (H.subgroupOf K)
  rw [hψ₀, card_involutions_psl2Borel, hinv, hcard] at hinv'
  have hpos : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hQ4' : 4 ≤ Nat.card Q := hQ4
  have hinv'' : 2 ^ a - 1 = Nat.card Q - 1 := hinv'
  have hQ : Nat.card Q = 2 ^ a := by omega
  have hstruct := LinearModel.linear_rank_one_point_structure (K := k) a ha hcard
  have htwo : ∀ a b c d : ℙ k (Fin 2 → k), a ≠ b → c ≠ d →
      ∃ g : PSL2MatrixGroup k, g • a = c ∧ g • b = d :=
    fun _ _ _ _ hab hcd => MulAction.is_two_pretransitive_iff.mp hstruct.2.1 hab hcd
  have hdeg : Nat.card (ℙ k (Fin 2 → k)) = Nat.card k + 1 := hstruct.2.2.1
  have hthree : ∀ a b : ℙ k (Fin 2 → k), ∃ c, c ≠ a ∧ c ≠ b := by
    let : Finite (ℙ k (Fin 2 → k)) := Nat.finite_of_card_ne_zero (by omega)
    have h4 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    exact exists_ne_ne_of_three_le_card (by rw [hdeg, hcard]; omega)
  have hKB : K ⊓ B = X := by
    refine proper_pair_hull_inf_pair_stabilizer_eq h hcomm hsmallerR1 hbeta ht hproper ψ _ _
      hψ₀ hψ₁ ?_
    rw [← LinearModel.torus_eq_borel_inf_stabilizer_zero, LinearModel.card_torus, hcard, hQ]
  have htK : t ∈ K := minimalLocalFailureProperPair_flip_mem H z beta t
  obtain ⟨f, hf, hfeq, hfα, hfβ⟩ := aligned_orbit_equiv H K (flip_coset_eq H ht) htK ψ hψ₀ hψ₁
    htwo hthree LinearModel.infinity_ne_zero
  refine ⟨hQ, hKB, k, inferInstance, inferInstance, hcard.trans hQ.symm, ψ, hψ₀, hψ₁, ?_, f, hf,
    hfeq, hfα, hfβ, ?_⟩
  · rw [pair_stabilizer_subgroupOf_map H K ht, hψ₀, hψ₁,
      LinearModel.torus_eq_borel_inf_stabilizer_zero]
  · rw [Nat.card_congr f, hdeg, hcard, hQ]


theorem proper_pair_suzuki_branch
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hO : CFSG.oddCore (minimalLocalFailureProperPairHull H z beta t) = ⊥)
    {m : ℕ} (e₀ : minimalLocalFailureProperPairHull H z beta t ≃* SuzukiMatrixGroup m) :
    let B := pairPointStabilizer H beta
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    Nat.card Q = 2 ^ (2 * m + 1) ∧ K ⊓ B = X ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (hk : Nat.card k = 2 ^ (2 * m + 1)),
        ∃ ψ : K ≃* CFSG.Blueprint.suzukiGroup m k,
          (H.subgroupOf K).map ψ.toMonoidHom = CFSG.LieType.Ree.suzukiB m k ∧
          ((rightConjugate H t).subgroupOf K).map ψ.toMonoidHom =
            MulAction.stabilizer (CFSG.Blueprint.suzukiGroup m k)
              (⟨CFSG.LieType.Ree.suzukiLine m k 0 0,
                CFSG.LieType.Ree.suzukiLine_mem_suzukiOmega m k 0 0⟩ :
                  CFSG.LieType.Ree.suzukiOmegaSub hk) ∧
          (B.subgroupOf K).map ψ.toMonoidHom = CFSG.LieType.Ree.suzukiT m k ∧
          ∃ f : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} ≃
              CFSG.LieType.Ree.suzukiOmegaSub hk,
            (∀ (x : K) (ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
              (ω : rightCosetSpace H) = rightCosetMk H x →
                f ω = (ψ x)⁻¹ • (⟨CFSG.LieType.Ree.suzukiInfty k,
                  CFSG.LieType.Ree.suzukiInfty_mem_suzukiOmega m k⟩ :
                    CFSG.LieType.Ree.suzukiOmegaSub hk)) ∧
            (∀ (x : K) (ω ω' : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
              (ω' : rightCosetSpace H) = rightCosetTranslate H ω x → f ω' = (ψ x)⁻¹ • f ω) ∧
            (∀ ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω},
              (ω : rightCosetSpace H) = rightCosetMk H 1 →
                f ω = ⟨CFSG.LieType.Ree.suzukiInfty k,
                  CFSG.LieType.Ree.suzukiInfty_mem_suzukiOmega m k⟩) ∧
            (∀ ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω},
              (ω : rightCosetSpace H) = beta →
                f ω = ⟨CFSG.LieType.Ree.suzukiLine m k 0 0,
                  CFSG.LieType.Ree.suzukiLine_mem_suzukiOmega m k 0 0⟩) ∧
            Nat.card {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} =
              Nat.card Q ^ 2 + 1 := by
  intro B X K Q
  let k := GaloisField 2 (2 * m + 1)
  have hk : Nat.card k = 2 ^ (2 * m + 1) := GaloisField.card 2 (2 * m + 1) (by omega)
  let e : K ≃* CFSG.Blueprint.suzukiGroup m k :=
    e₀.trans (SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hk).symm
  have hSPA := SuzukiModel.suzukiPointAction_suzukiGroup (a := m) hk
  obtain ⟨S₀, hS₀U⟩ := hSPA.exists_sylow
  have hq : 1 < 2 ^ (2 * m + 1) := Nat.one_lt_two_pow (by omega)
  have hS₀ : Subgroup.normalizer ((S₀ : Subgroup (CFSG.Blueprint.suzukiGroup m k)) :
      Set (CFSG.Blueprint.suzukiGroup m k)) =
      MulAction.stabilizer (CFSG.Blueprint.suzukiGroup m k)
        (⟨CFSG.LieType.Ree.suzukiInfty k, CFSG.LieType.Ree.suzukiInfty_mem_suzukiOmega m k⟩ :
          CFSG.LieType.Ree.suzukiOmegaSub hk) := by
    rw [hS₀U]
    exact hSPA.normalizer_eq_stabilizer hq
  have htwo : ∀ a b c d : CFSG.LieType.Ree.suzukiOmegaSub hk, a ≠ b → c ≠ d →
      ∃ g : CFSG.Blueprint.suzukiGroup m k, g • a = c ∧ g • b = d :=
    fun _ _ _ _ hab hcd => MulAction.is_two_pretransitive_iff.mp hSPA.isMultiplyPretransitive hab hcd
  obtain ⟨ψ, hψ₀, hψ₁⟩ := proper_pair_hull_aligned_iso h hcomm hsmallerR1 hbeta ht hproper hO e S₀
    _ hS₀ htwo _ _ hSPA.ne
  obtain ⟨-, hQ4, -⟩ := proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  have hinv := proper_pair_card_point_involutions h hcomm hbeta ht hproper
  have hinv' := card_involutions_map_mulEquiv ψ (H.subgroupOf K)
  rw [hψ₀, hinv] at hinv'
  have hcount := hSPA.ncard_involutions
  rw [← Nat.card_coe_set_eq] at hcount
  have hinv'' : 2 ^ (2 * m + 1) - 1 = Nat.card Q - 1 := hcount.symm.trans hinv'
  have hQ4' : 4 ≤ Nat.card Q := hQ4
  have hQ : Nat.card Q = 2 ^ (2 * m + 1) := by omega
  have hdeg := hSPA.card_eq
  have hthree : ∀ a b : CFSG.LieType.Ree.suzukiOmegaSub hk, ∃ c, c ≠ a ∧ c ≠ b := by
    let : Finite (CFSG.LieType.Ree.suzukiOmegaSub hk) := Nat.finite_of_card_ne_zero (by omega)
    have h3 : 3 ≤ (2 ^ (2 * m + 1)) ^ 2 + 1 := by nlinarith
    exact exists_ne_ne_of_three_le_card (by rw [hdeg]; exact h3)
  have hKB : K ⊓ B = X := by
    refine proper_pair_hull_inf_pair_stabilizer_eq h hcomm hsmallerR1 hbeta ht hproper ψ _ _
      hψ₀ hψ₁ ?_
    rw [hSPA.stabilizer_inf_stabilizer, hSPA.card_T, hQ]
  have htK : t ∈ K := minimalLocalFailureProperPair_flip_mem H z beta t
  obtain ⟨f, hf, hfeq, hfα, hfβ⟩ := aligned_orbit_equiv H K (flip_coset_eq H ht) htK ψ hψ₀ hψ₁
    htwo hthree hSPA.ne
  refine ⟨hQ, hKB, k, inferInstance, inferInstance, hk, ψ, ?_, hψ₁, ?_, f, hf, hfeq, hfα, hfβ, ?_⟩
  · rw [hψ₀, (CFSG.LieType.Ree.suzuki_ovoid_stabilizer hk).2]
  · rw [pair_stabilizer_subgroupOf_map H K ht, hψ₀, hψ₁, hSPA.stabilizer_inf_stabilizer]
  · rw [Nat.card_congr f, hdeg, hQ]


theorem proper_pair_involution_clauses
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hKB : minimalLocalFailureProperPairHull H z beta t ⊓ pairPointStabilizer H beta =
      rightInvolutionCommutatorSubgroup t (pairOddCore H beta))
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) :
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    let E := Q ⊓ Subgroup.centralizer ({u} : Set G)
    u ∉ K ∧ (Q ≤ Subgroup.centralizer {u} → K ≤ Subgroup.centralizer {u}) ∧
      (¬ Q ≤ Subgroup.centralizer {u} → 4 ≤ Nat.card E ∧ Nat.card Q = Nat.card E ^ 2 ∧
        ∃ e : ℕ, Even e ∧ Nat.card Q = 2 ^ e) := by
  intro K Q E
  obtain ⟨hsimple, hnonab⟩ := minimalLocalFailure_nonabelian_simple h
  obtain ⟨hQ, ⟨e, hQe⟩, hQ4, hQclass, hXB, hXnormal, hXcyclic, hXcard, hXregular, htB⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨hE4, hcentralcase, hnoncentral, -, -, -, ⟨tu, ⟨x, hxX, rfl⟩, htu, -, -⟩, -⟩ :=
    PairInvolutionFixedField.pair_involution_fixed_field_and_orbit hsimple hnonab h.local_datum
      h.central_sylow hQ hQe hQ4 hQclass hbeta ht hXB hXnormal hXcyclic hXcard hXregular htB huB hu
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hXodd, -⟩ :=
    proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  refine ⟨fun huK => ?_, fun hQu => ?_, fun hQu => ?_⟩
  · have huX : u ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta) := by
      rw [← hKB]
      exact ⟨huK, huB⟩
    have hdvd := Subgroup.orderOf_dvd_natCard _ huX
    rw [hu] at hdvd
    exact (Nat.not_even_iff_odd.mpr hXodd) (even_iff_two_dvd.mpr hdvd)
  · obtain ⟨-, hX0⟩ := hcentralcase hQu
    have hXu : rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ≤
        Subgroup.centralizer {u} := by
      rw [← hX0]
      exact inf_le_right
    obtain ⟨-, -, -, -, -, -, hzQ⟩ := proper_pair_point_root h hcomm hbeta ht hproper
    apply (Subgroup.closure_le _).mpr
    rintro y ((hyz | hyt) | hy)
    · rw [hyz]
      exact hQu hzQ
    · rw [show y = t * x * x⁻¹ by rw [hyt, mul_inv_cancel_right]]
      exact mul_mem (Subgroup.mem_centralizer_singleton_iff.mpr htu.eq) (inv_mem (hXu hxX))
    · exact hXu hy
  · obtain ⟨heven, -, hQE⟩ := hnoncentral hQu
    exact ⟨hE4, hQE, e, heven, hQe⟩


theorem minimalLocalFailure_proper_pair_hull_linear_or_suzuki
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let B := pairPointStabilizer H beta
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    Group.IsPerfect K ∧ CFSG.oddCore K = ⊥ ∧ K ⊓ B = X ∧
    ((∃ e : ℕ, 2 ≤ e ∧ Nat.card Q = 2 ^ e ∧ Nonempty (K ≃* PSL2BinaryMatrixGroup e) ∧
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Nat.card Q ∧
          ∃ ψ : K ≃* PSL2MatrixGroup k,
            (H.subgroupOf K).map ψ.toMonoidHom = CFSG.GorensteinWalter.psl2Borel k ∧
            ((rightConjugate H t).subgroupOf K).map ψ.toMonoidHom =
              MulAction.stabilizer (PSL2MatrixGroup k)
                (CFSG.GorensteinWalter.psl2ProjectiveZero k) ∧
            (B.subgroupOf K).map ψ.toMonoidHom = LinearModel.torus k ∧
            ∃ f : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} ≃
                ℙ k (Fin 2 → k),
              (∀ (x : K) (ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
                (ω : rightCosetSpace H) = rightCosetMk H x →
                  f ω = (ψ x)⁻¹ • CFSG.GorensteinWalter.psl2ProjectiveInfinity k) ∧
              (∀ (x : K) (ω ω' : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
                (ω' : rightCosetSpace H) = rightCosetTranslate H ω x → f ω' = (ψ x)⁻¹ • f ω) ∧
              (∀ ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω},
                (ω : rightCosetSpace H) = rightCosetMk H 1 →
                  f ω = CFSG.GorensteinWalter.psl2ProjectiveInfinity k) ∧
              (∀ ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω},
                (ω : rightCosetSpace H) = beta →
                  f ω = CFSG.GorensteinWalter.psl2ProjectiveZero k) ∧
              Nat.card {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} =
                Nat.card Q + 1) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card Q = 2 ^ (2 * m + 1) ∧ Nonempty (K ≃* SuzukiMatrixGroup m) ∧
        ∃ (k : Type) (_ : Field k) (_ : Finite k) (hk : Nat.card k = 2 ^ (2 * m + 1)),
          ∃ ψ : K ≃* CFSG.Blueprint.suzukiGroup m k,
            (H.subgroupOf K).map ψ.toMonoidHom = CFSG.LieType.Ree.suzukiB m k ∧
            ((rightConjugate H t).subgroupOf K).map ψ.toMonoidHom =
              MulAction.stabilizer (CFSG.Blueprint.suzukiGroup m k)
                (⟨CFSG.LieType.Ree.suzukiLine m k 0 0,
                  CFSG.LieType.Ree.suzukiLine_mem_suzukiOmega m k 0 0⟩ :
                    CFSG.LieType.Ree.suzukiOmegaSub hk) ∧
            (B.subgroupOf K).map ψ.toMonoidHom = CFSG.LieType.Ree.suzukiT m k ∧
            ∃ f : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} ≃
                CFSG.LieType.Ree.suzukiOmegaSub hk,
              (∀ (x : K) (ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
                (ω : rightCosetSpace H) = rightCosetMk H x →
                  f ω = (ψ x)⁻¹ • (⟨CFSG.LieType.Ree.suzukiInfty k,
                    CFSG.LieType.Ree.suzukiInfty_mem_suzukiOmega m k⟩ :
                      CFSG.LieType.Ree.suzukiOmegaSub hk)) ∧
              (∀ (x : K) (ω ω' : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
                (ω' : rightCosetSpace H) = rightCosetTranslate H ω x → f ω' = (ψ x)⁻¹ • f ω) ∧
              (∀ ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω},
                (ω : rightCosetSpace H) = rightCosetMk H 1 →
                  f ω = ⟨CFSG.LieType.Ree.suzukiInfty k,
                    CFSG.LieType.Ree.suzukiInfty_mem_suzukiOmega m k⟩) ∧
              (∀ ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω},
                (ω : rightCosetSpace H) = beta →
                  f ω = ⟨CFSG.LieType.Ree.suzukiLine m k 0 0,
                    CFSG.LieType.Ree.suzukiLine_mem_suzukiOmega m k 0 0⟩) ∧
              Nat.card {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} =
                Nat.card Q ^ 2 + 1)) ∧
    B ≤ Subgroup.normalizer (K : Set G) ∧ B ≤ Subgroup.normalizer (X : Set G) ∧
    ∀ u ∈ B, orderOf u = 2 →
      u ∉ K ∧ (Q ≤ Subgroup.centralizer {u} → K ≤ Subgroup.centralizer {u}) ∧
        (¬ Q ≤ Subgroup.centralizer {u} →
          4 ≤ Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ∧
          Nat.card Q = Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ^ 2 ∧
          ∃ (k : Type) (_ : Field k) (_ : Finite k),
            Nat.card k = Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ^ 2 ∧
            Nonempty (K ≃* PSL2MatrixGroup k)) := by
  intro B X K Q
  obtain ⟨hperfect, hO, a, ha, hmodel⟩ :=
    proper_pair_hull_linear_or_suzuki_iso h hcomm hsmallerR1 hbeta ht hproper
  have hnorm := original_pair_hull_normalized h hcomm hbeta ht hproper
  have hXnorm := (original_pair_commutator_normal h hbeta ht).1
  rcases hmodel with he₀ | ⟨m, hm, he₀⟩
  · obtain ⟨e₀⟩ := he₀
    obtain ⟨hQ, hKB, rest⟩ :=
      proper_pair_linear_branch h hcomm hsmallerR1 hbeta ht hproper hO ha e₀
    refine ⟨hperfect, hO, hKB, Or.inl ⟨a, ha, hQ, ⟨e₀⟩, rest⟩, hnorm, hXnorm, ?_⟩
    intro u huB hu
    obtain ⟨h1, h2, h3⟩ :=
      proper_pair_involution_clauses h hcomm hsmallerR1 hbeta ht hproper hKB huB hu
    refine ⟨h1, h2, fun hQu => ?_⟩
    obtain ⟨hE4, hQE, -⟩ := h3 hQu
    obtain ⟨k, hkF, hkfin, hk, ψ, -⟩ := rest
    exact ⟨hE4, hQE, k, hkF, hkfin, hk.trans hQE, ⟨ψ⟩⟩
  · obtain ⟨e₀⟩ := he₀
    have hm1 : 1 ≤ m := by omega
    obtain ⟨hQ, hKB, rest⟩ :=
      proper_pair_suzuki_branch h hcomm hsmallerR1 hbeta ht hproper hO e₀
    refine ⟨hperfect, hO, hKB, Or.inr ⟨m, hm1, hQ, ⟨e₀⟩, rest⟩, hnorm, hXnorm, ?_⟩
    intro u huB hu
    obtain ⟨h1, h2, h3⟩ :=
      proper_pair_involution_clauses h hcomm hsmallerR1 hbeta ht hproper hKB huB hu
    refine ⟨h1, h2, fun hQu => ?_⟩
    obtain ⟨-, -, e, ⟨r, hr⟩, hQe⟩ := h3 hQu
    have hexp : 2 * m + 1 = e := Nat.pow_right_injective (le_refl 2) (hQ.symm.trans hQe)
    omega

end CFSG.ShultStronglyClosedTI.ProperPairModel
