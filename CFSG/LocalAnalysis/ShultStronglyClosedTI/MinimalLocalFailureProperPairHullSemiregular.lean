module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairLinearOrSuzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicSemiregular
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInverters

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.CyclicPair
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

variable {G : Type} [Group G] [Finite G]

theorem proper_pair_hull_involution_conj
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {y : G} (hyK : y ∈ minimalLocalFailureProperPairHull H z beta t) (hy : orderOf y = 2) :
    ∃ k ∈ minimalLocalFailureProperPairHull H z beta t, rightConjugateElem z k = y := by
  have hM := minimalLocalFailureProperPair_stronglyEmbedded h hbeta ht hproper
  have hM' := native_strong_embedding_of_order_conditions hM
  have hzK := minimalLocalFailureProperPair_distinguished_mem H z beta t
  have hzI : IsInvolution (⟨z, hzK⟩ : minimalLocalFailureProperPairHull H z beta t) := by
    have hz2 : orderOf (⟨z, hzK⟩ : minimalLocalFailureProperPairHull H z beta t) = 2 :=
      (Subgroup.orderOf_mk z hzK).trans h.local_datum.distinguished_order
    exact ⟨(orderOf_eq_prime_iff.mp hz2).2, (orderOf_eq_prime_iff.mp hz2).1⟩
  have hyI : IsInvolution (⟨y, hyK⟩ : minimalLocalFailureProperPairHull H z beta t) := by
    have hy2 : orderOf (⟨y, hyK⟩ : minimalLocalFailureProperPairHull H z beta t) = 2 :=
      (Subgroup.orderOf_mk y hyK).trans hy
    exact ⟨(orderOf_eq_prime_iff.mp hy2).2, (orderOf_eq_prime_iff.mp hy2).1⟩
  obtain ⟨g, hg⟩ := hM'.involutions_conjugate hzI hyI
  refine ⟨g, g.2, ?_⟩
  have h1 := congrArg Subtype.val hg
  simpa [rightConjugateElem] using h1

theorem proper_pair_hull_involution_fixed
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {y : G} (hyK : y ∈ minimalLocalFailureProperPairHull H z beta t) (hy : orderOf y = 2)
    {γ : rightCosetSpace H} (hγ : rightCosetTranslate H γ y = γ) :
    ∃ k ∈ minimalLocalFailureProperPairHull H z beta t, rightCosetMk H k = γ := by
  obtain ⟨k, hkK, rfl⟩ := proper_pair_hull_involution_conj h hbeta ht hproper hyK hy
  have hfixk : rightCosetTranslate H (rightCosetMk H k) (rightConjugateElem z k) =
      rightCosetMk H k := by
    rw [rightCosetTranslate_mk, rightConjugateElem, PairInvolutionFixedField.rightCosetMk_eq_iff]
    have h1 : k * (k * (k⁻¹ * z * k))⁻¹ = z⁻¹ := by group
    rw [h1]
    exact H.inv_mem h.local_datum.distinguished_mem
  have huniq := ((involution_point_unique_containment_action h.local_datum.distinguished_mem
    h.local_datum.distinguished_order).2 h.local_datum.unique_containment).2.1
  obtain ⟨ω₀, -, hω₀⟩ := huniq _ ⟨k, rfl⟩
  have h1 := hω₀ γ (by
    change pointRightCosetMul H γ (rightConjugateElem z k) = γ
    rw [pointRightCosetMul_eq_translate]
    exact hγ)
  have h2 := hω₀ (rightCosetMk H k) (by
    change pointRightCosetMul H (rightCosetMk H k) (rightConjugateElem z k) = rightCosetMk H k
    rw [pointRightCosetMul_eq_translate]
    exact hfixk)
  exact ⟨k, hkK, h2.trans h1.symm⟩

theorem proper_pair_hull_inverters
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    OddPrimeInverters.OddPrimeInvertersAndSplitFusion
      (minimalLocalFailureProperPairHull H z beta t)
      (Nat.card (minimalLocalFailurePairActionPointHull H z)) := by
  obtain ⟨-, -, -, hmodel, -⟩ :=
    minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1 hbeta ht hproper
  rcases hmodel with ⟨e, he, hQe, ⟨e₀⟩, -⟩ | ⟨m, hm, hQm, ⟨e₀⟩, -⟩
  · have hk : Nat.card (BinaryGaloisField e) = 2 ^ e := by
      simpa [BinaryGaloisField] using GaloisField.card 2 e (by omega)
    have h1 := OddPrimeInverters.oddPrimeInvertersAndSplitFusion_of_mulEquiv_psl2 he hk e₀
    rwa [hk, ← hQe] at h1
  · have h1 := OddPrimeInverters.oddPrimeInvertersAndSplitFusion_of_mulEquiv_suzukiMatrixGroup hm e₀
    rwa [← hQm] at h1

theorem proper_pair_hull_split_prime_fixed
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {y : G} (hyK : y ∈ minimalLocalFailureProperPairHull H z beta t) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card (minimalLocalFailurePairActionPointHull H z) - 1)
    (hy : orderOf y = p) {γ : rightCosetSpace H} (hγ : rightCosetTranslate H γ y = γ) :
    ∃ k ∈ minimalLocalFailureProperPairHull H z beta t, rightCosetMk H k = γ := by
  have hinv := proper_pair_hull_inverters h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, -, -, hXcard, -, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, -, -, -, -, hXK, -⟩ :=
    proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, hfixX, -⟩ :=
    CyclicSemiregular.minimalLocalFailure_proper_pair_cyclic_semiregularity h hcomm hsmallerR1
      hbeta ht hproper
  have htK : t ∈ minimalLocalFailureProperPairHull H z beta t :=
    minimalLocalFailureProperPair_flip_mem H z beta t
  have hcardXK : Nat.card ((rightInvolutionCommutatorSubgroup t (pairOddCore H beta)).subgroupOf
      (minimalLocalFailureProperPairHull H z beta t)) =
      Nat.card (minimalLocalFailurePairActionPointHull H z) - 1 := by
    rw [← hXcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv
  have hyord : orderOf (⟨y, hyK⟩ : minimalLocalFailureProperPairHull H z beta t) = p :=
    (Subgroup.orderOf_mk y hyK).trans hy
  obtain ⟨g, hg⟩ := hinv.exists_conj_mem _ hcardXK p hp hp2 hpq _ hyord
  have hx'X : (g : G) * y * (g : G)⁻¹ ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta) :=
    hg
  have hx'1 : (g : G) * y * (g : G)⁻¹ ≠ 1 := by
    intro h1
    have hy1 : y = (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * g := by group
    rw [h1, mul_one, inv_mul_cancel] at hy1
    rw [hy1, orderOf_one] at hy
    exact hp.one_lt.ne hy
  have hfix : rightCosetTranslate H (rightCosetTranslate H γ (g : G)⁻¹)
      ((g : G) * y * (g : G)⁻¹) = rightCosetTranslate H γ (g : G)⁻¹ := by
    rw [rightCosetTranslate_mul, show (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) = y * (g : G)⁻¹ by
      group, ← rightCosetTranslate_mul, hγ]
  have hin : rightCosetTranslate H γ (g : G)⁻¹ ∈ ({rightCosetMk H 1, beta} : Set _) := by
    rw [← hfixX _ hx'X hx'1]
    exact hfix
  have hγeq : γ = rightCosetTranslate H (rightCosetTranslate H γ (g : G)⁻¹) (g : G) := by
    rw [rightCosetTranslate_mul, inv_mul_cancel, rightCosetTranslate_one]
  rcases hin with hα | hβ
  · refine ⟨g, g.2, ?_⟩
    rw [hγeq, hα, rightCosetTranslate_mk, one_mul]
  · have hβ' : rightCosetTranslate H γ (g : G)⁻¹ = rightCosetMk H t :=
      (Set.mem_singleton_iff.mp hβ).trans (flip_coset_eq H ht)
    refine ⟨t * g, Subgroup.mul_mem _ htK g.2, ?_⟩
    rw [hγeq, hβ', rightCosetTranslate_mk]


omit [Finite G] in
theorem exists_ne_one_conj_eq_of_not_dvd {Q : Subgroup G} [Finite Q] {y : G} {p : ℕ}
    (hp : p.Prime) (hy : y ^ p = 1) (hyQ : ∀ s ∈ Q, y * s * y⁻¹ ∈ Q)
    (hyQ' : ∀ s ∈ Q, y⁻¹ * s * y ∈ Q) (hpQ : ¬ p ∣ Nat.card Q - 1) :
    ∃ s ∈ Q, s ≠ 1 ∧ y * s * y⁻¹ = s := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hne : ∀ s : G, s ≠ 1 → ∀ a : G, a * s * a⁻¹ ≠ 1 := fun s hs a h1 =>
    hs (by rw [show s = a⁻¹ * (a * s * a⁻¹) * a by group, h1]; group)
  let σ : Equiv.Perm {s : G // s ∈ Q ∧ s ≠ 1} :=
    { toFun := fun s => ⟨y * s.1 * y⁻¹, hyQ _ s.2.1, hne _ s.2.2 y⟩
      invFun := fun s => ⟨y⁻¹ * s.1 * y, hyQ' _ s.2.1, by
        simpa only [inv_inv] using hne _ s.2.2 y⁻¹⟩
      left_inv := fun s => Subtype.ext (by simp only; group)
      right_inv := fun s => Subtype.ext (by simp only; group) }
  have hσpow : ∀ n : ℕ, ∀ s, ((σ ^ n) s).1 = y ^ n * s.1 * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [pow_succ', Equiv.Perm.mul_apply]
      change y * ((σ ^ n) s).1 * y⁻¹ = _
      rw [ih, pow_succ']
      group
  have hσp : σ ^ p ^ 1 = 1 := by
    ext s
    rw [pow_one, hσpow, hy, one_mul, inv_one, mul_one]
    rfl
  have : Finite {s : G // s ∈ Q ∧ s ≠ 1} :=
    Finite.of_injective (fun s => (⟨s.1, s.2.1⟩ : Q)) (fun a b hab => Subtype.ext
      (congrArg Subtype.val hab : _))
  let : Fintype {s : G // s ∈ Q ∧ s ≠ 1} := Fintype.ofFinite _
  have hcard : Fintype.card {s : G // s ∈ Q ∧ s ≠ 1} = Nat.card Q - 1 := by
    rw [← Nat.card_eq_fintype_card, ← PairInvolutionFixedField.card_diff_one Q]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  obtain ⟨s, hs⟩ := Equiv.Perm.exists_fixed_point_of_prime (n := 1) (by rw [hcard]; exact hpQ) hσp
  exact ⟨s.1, s.2.1, s.2.2, congrArg Subtype.val hs⟩


theorem proper_pair_hull_nonsplit_prime_no_fixed
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {y : G} (hyK : y ∈ minimalLocalFailureProperPairHull H z beta t) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card (minimalLocalFailurePairActionPointHull H z) - 1)
    (hy : orderOf y = p) (γ : rightCosetSpace H) : rightCosetTranslate H γ y ≠ γ := by
  intro hγ
  let : Fact p.Prime := ⟨hp⟩
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  obtain ⟨hQH, -, hQnormal, -, hQp, -, -⟩ := proper_pair_point_root h hcomm hbeta ht hproper
  obtain ⟨-, -, hQclass, -⟩ := proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  have hconjQ : ∀ a ∈ H, ∀ s ∈ Q, a * s * a⁻¹ ∈ Q := fun a ha s hs =>
    hQnormal.conj_mem ⟨s, hQH hs⟩ hs ⟨a, ha⟩
  obtain ⟨g, rfl⟩ := PairInvolutionFixedField.exists_rightCosetMk γ
  have hy₀H : g * y * g⁻¹ ∈ H := (PairInvolutionFixedField.translate_mk_fixed_iff H g y).mp hγ
  have hy₀ord : orderOf (g * y * g⁻¹) = p := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hy
  obtain ⟨s₀, hs₀Q, hs₀1, hs₀c⟩ := exists_ne_one_conj_eq_of_not_dvd hp
    (by rw [← hy₀ord]; exact pow_orderOf_eq_one _) (hconjQ _ hy₀H)
    (fun s hs => by simpa only [inv_inv] using hconjQ _ (H.inv_mem hy₀H) s hs) hpq
  have hinv := proper_pair_hull_inverters h hcomm hsmallerR1 hbeta ht hproper
  have hyKord : orderOf (⟨y, hyK⟩ : minimalLocalFailureProperPairHull H z beta t) = p :=
    (Subgroup.orderOf_mk y hyK).trans hy
  obtain ⟨rK, hrK2, hrKinv⟩ :=
    hinv.exists_involution_inverts ⟨y, hyK⟩ (hyKord ▸ hp) (hyKord ▸ hp2)
  have hr2 : orderOf (rK : G) = 2 := (Subgroup.orderOf_coe rK).trans hrK2
  have hrinv : (rK : G) * y * (rK : G)⁻¹ = y⁻¹ := congrArg Subtype.val hrKinv
  obtain ⟨k, -, hkr⟩ := proper_pair_hull_involution_conj h hbeta ht hproper rK.2 hr2
  have hr₀inv : (g * rK * g⁻¹) * (g * y * g⁻¹) * (g * rK * g⁻¹)⁻¹ = (g * y * g⁻¹)⁻¹ := by
    calc (g * rK * g⁻¹) * (g * y * g⁻¹) * (g * rK * g⁻¹)⁻¹
        = g * ((rK : G) * y * (rK : G)⁻¹) * g⁻¹ := by group
      _ = (g * y * g⁻¹)⁻¹ := by rw [hrinv]; group
  obtain ⟨h₁, hh₁⟩ : ∃ h₁ : H, (h₁ : G)⁻¹ * z * h₁ = s₀ := by
    have hs₀class : s₀ ∈ conjugacyWithin H z := by
      rw [← hQclass]
      exact ⟨hs₀Q, hs₀1⟩
    exact hs₀class
  have hfail := minimalLocalFailure_ambient_right_conjugate h (h₁ : G)
  rw [rightConjugate_eq_self_of_mem h₁.2] at hfail
  have hz₁ : rightConjugateElem z (h₁ : G) = s₀ := hh₁
  rw [hz₁] at hfail
  obtain ⟨S, hzS, hzcenter⟩ := hfail.central_sylow
  have hAH : Subgroup.zpowers (g * y * g⁻¹) ≤ H := (Subgroup.zpowers_le).mpr hy₀H
  have hAs : rightConjugate (Subgroup.zpowers (g * y * g⁻¹)) s₀ =
      Subgroup.zpowers (g * y * g⁻¹) := by
    apply rightConjugate_eq_self_of_mem_normalizer
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    congr 1
    change s₀ * (g * y * g⁻¹) * s₀⁻¹ = g * y * g⁻¹
    have h1 : (g * y * g⁻¹) * s₀ = s₀ * (g * y * g⁻¹) := by
      calc (g * y * g⁻¹) * s₀
          = ((g * y * g⁻¹) * s₀ * (g * y * g⁻¹)⁻¹) * (g * y * g⁻¹) := by group
        _ = s₀ * (g * y * g⁻¹) := by rw [hs₀c]
    rw [← h1]
    group
  have hr₀N : g * rK * g⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers (g * y * g⁻¹) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers ((g * rK * g⁻¹) * (g * y * g⁻¹) * (g * rK * g⁻¹)⁻¹) = _
    rw [hr₀inv, Subgroup.zpowers_inv]
  have hr₀D : g * rK * g⁻¹ ∈ involutionPointClass s₀ := by
    refine ⟨(h₁ : G)⁻¹ * k * g⁻¹, ?_⟩
    rw [← hz₁, ← hkr]
    simp only [rightConjugateElem]
    group
  obtain ⟨⟨δ, hδ, -⟩, hδA⟩ := involution_point_invariant_subgroup_normalizer_fixed_points
    hfail.local_datum S hzS hzcenter _ hAH hAs ⟨hr₀D, hr₀N⟩
  have hAδ := (hδA δ hδ).2
  obtain ⟨w, rfl⟩ := PairInvolutionFixedField.exists_rightCosetMk δ
  have hy₁H : w * (g * y * g⁻¹) * w⁻¹ ∈ H := by
    have h1 := hAδ (Subgroup.mem_zpowers (g * y * g⁻¹))
    rw [mem_rightCosetStabilizer_iff] at h1
    exact (PairInvolutionFixedField.translate_mk_fixed_iff H w _).mp h1
  have hr₁H : w * (g * rK * g⁻¹) * w⁻¹ ∈ H := by
    have h1 : rightCosetTranslate H (rightCosetMk H w) (g * rK * g⁻¹) = rightCosetMk H w := by
      rw [← pointRightCosetMul_eq_translate]
      exact hδ
    exact (PairInvolutionFixedField.translate_mk_fixed_iff H w _).mp h1
  have hr₁D : w * (g * rK * g⁻¹) * w⁻¹ ∈ involutionPointClass z := by
    refine ⟨k * g⁻¹ * w⁻¹, ?_⟩
    rw [← hkr]
    simp only [rightConjugateElem]
    group
  have hDH := ((involution_point_unique_containment_action h.local_datum.distinguished_mem
    h.local_datum.distinguished_order).1.mp h.local_datum.unique_containment).2
  have hr₁Q : w * (g * rK * g⁻¹) * w⁻¹ ∈ Q := by
    have h1 : w * (g * rK * g⁻¹) * w⁻¹ ∈ involutionPointClass z ∩ (H : Set G) := ⟨hr₁D, hr₁H⟩
    rw [hDH] at h1
    obtain ⟨c, hcH, hc⟩ := h1
    have h2 : w * (g * rK * g⁻¹) * w⁻¹ ∈ conjugacyWithin H z := ⟨⟨c, hcH⟩, hc⟩
    rw [← hQclass] at h2
    exact h2.1
  set y₁ := w * (g * y * g⁻¹) * w⁻¹ with hy₁
  set r₁ := w * (g * rK * g⁻¹) * w⁻¹ with hr₁
  have hr₁inv : r₁ * y₁ * r₁⁻¹ = y₁⁻¹ := by
    calc r₁ * y₁ * r₁⁻¹ = w * ((g * rK * g⁻¹) * (g * y * g⁻¹) * (g * rK * g⁻¹)⁻¹) * w⁻¹ := by
          simp only [hr₁, hy₁]; group
      _ = y₁⁻¹ := by rw [hr₀inv]; simp only [hy₁]; group
  have hQ1 : y₁⁻¹ * r₁ * y₁⁻¹⁻¹ ∈ Q := hconjQ _ (H.inv_mem hy₁H) _ hr₁Q
  have hsq : y₁⁻¹ * y₁⁻¹ ∈ Q := by
    have h1 : y₁⁻¹ * r₁ * y₁⁻¹⁻¹ * r₁⁻¹ = y₁⁻¹ * y₁⁻¹ := by
      rw [inv_inv]
      calc y₁⁻¹ * r₁ * y₁ * r₁⁻¹ = y₁⁻¹ * (r₁ * y₁ * r₁⁻¹) := by group
        _ = y₁⁻¹ * y₁⁻¹ := by rw [hr₁inv]
    rw [← h1]
    exact Q.mul_mem hQ1 (Q.inv_mem hr₁Q)
  obtain ⟨n, hn⟩ := hQp ⟨y₁⁻¹ * y₁⁻¹, hsq⟩
  have hn' : (y₁⁻¹ * y₁⁻¹) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hy₁ord : orderOf y₁ = p := by
    rw [hy₁, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hy₀ord
  have hpow : y₁ ^ (2 ^ (n + 1)) = 1 := by
    have h1 : (y₁⁻¹ * y₁⁻¹) ^ 2 ^ n = (y₁ ^ (2 ^ (n + 1)))⁻¹ := by
      rw [← sq, ← inv_pow, ← pow_mul, pow_succ', inv_pow]
    rw [h1, inv_eq_one] at hn'
    exact hn'
  have hdvd : p ∣ 2 ^ (n + 1) := hy₁ord ▸ orderOf_dvd_of_pow_eq_one hpow
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))


theorem proper_pair_hull_fixed_points_in_orbit
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {x : G} (hxK : x ∈ minimalLocalFailureProperPairHull H z beta t) (hx1 : x ≠ 1)
    {γ : rightCosetSpace H} (hγ : rightCosetTranslate H γ x = γ) :
    ∃ k ∈ minimalLocalFailureProperPairHull H z beta t, rightCosetMk H k = γ := by
  have hord1 : orderOf x ≠ 1 := fun h1 => hx1 (orderOf_eq_one_iff.mp h1)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord1
  have hord0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hy : orderOf (x ^ (orderOf x / p)) = p := orderOf_pow_orderOf_div hord0 hpdvd
  have hyK : x ^ (orderOf x / p) ∈ minimalLocalFailureProperPairHull H z beta t :=
    Subgroup.pow_mem _ hxK _
  have hyγ : rightCosetTranslate H γ (x ^ (orderOf x / p)) = γ := by
    rw [← mem_rightCosetStabilizer_iff] at hγ ⊢
    exact Subgroup.pow_mem _ hγ _
  by_cases hp2 : p = 2
  · subst hp2
    exact proper_pair_hull_involution_fixed h hbeta ht hproper hyK hy hyγ
  · by_cases hpq : p ∣ Nat.card (minimalLocalFailurePairActionPointHull H z) - 1
    · exact proper_pair_hull_split_prime_fixed h hcomm hsmallerR1 hbeta ht hproper hyK hp hp2
        hpq hy hyγ
    · exact (proper_pair_hull_nonsplit_prime_no_fixed h hcomm hsmallerR1 hbeta ht hproper hyK hp
        hp2 hpq hy γ hyγ).elim


end CFSG.ShultStronglyClosedTI.ProperPairModel
