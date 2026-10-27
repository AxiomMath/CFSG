module

public import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore
public import CFSG.RankThree.SteinbergR3EOddE7RationalStructure

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality
  finite_field_prime_power_characteristic)
open CFSG.ComponentClassification.UnbalancedCatalog (mem_zpowers_of_fixed)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open SteinbergBT (not_commute_fixedFieldImage)

variable {τ : Tag} {K : Type} [Field K]

theorem odd_entrywise_canonical_core_data_of_fixer {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    [Finite K] [CharP K ℓ] (σ : K ≃+* K)
    (hfixer : ∀ β : MulAut (adjointGroup τ K),
      (∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ fixedFieldImage τ σ → β j = j) →
        ∃ η : K ≃+* K, (∀ c, σ c = c → η c = c) ∧ β = entrywiseAdjointAut τ η) :
    fixedFieldImage τ σ ≤ adjointGroup τ K ∧ IsSimpleGroup (fixedFieldImage τ σ) ∧
    (¬∀ a b : fixedFieldImage τ σ, a * b = b * a) ∧
    Nonempty (↥((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) ≃*
      ↥(((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)))) ∧
    ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) ≤
      Subgroup.centralizer {entrywiseAdjointAut τ σ} ∧
    ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K))).subgroupOf
      (Subgroup.centralizer {entrywiseAdjointAut τ σ})).Normal ∧
    Subgroup.centralizer {entrywiseAdjointAut τ σ} ⊓
        Subgroup.centralizer ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
          (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) :
            Subgroup (MulAut (adjointGroup τ K))) : Set (MulAut (adjointGroup τ K))) =
      Subgroup.zpowers (entrywiseAdjointAut τ σ) := by
  classical
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hZ : Subgroup.center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  obtain ⟨-, -, -, hJΓ, -, -, -, hΓ'⟩ := Chevalley_coordinate_field_fixed_structure τ K hK2 σ
  set C := adjointGroup τ K with hC
  set δ := entrywiseAdjointAut τ σ with hδ
  set J := fixedFieldImage τ σ with hJ
  set Γ := entrywiseFixedGroup τ σ with hΓ
  set N := (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) with hN
  have hJC : J ≤ C := fun j hj => (mem_entrywiseFixedGroup.1 (hJΓ hj)).1
  have hδJ : ∀ j : C, (j : ModGL τ K) ∈ J → δ j = j := fun j hj =>
    Subtype.ext ((coe_entrywiseAdjointAut τ σ j).trans (mem_entrywiseFixedGroup.1 (hJΓ hj)).2)
  have hk2 : ringChar (fixSubfield σ) ≠ 2 := by
    intro h
    have h0 : ((2 : ℕ) : fixSubfield σ) = 0 := by
      rw [← h]
      exact ringChar.Nat.cast_ringChar
    apply Ring.two_ne_zero hK2
    have := congrArg (fixSubfield σ).subtype h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  have : IsSimpleGroup (adjointGroup τ (fixSubfield σ)) :=
    (odd_pinned_Chevalley_p_components τ (fixSubfield σ) hk2).1
  have eJ : J ≃* adjointGroup τ (fixSubfield σ) :=
    ((adjointGroup τ (fixSubfield σ)).equivMapOfInjective _ (baseChangeGL_injective _)).symm
  have hNδ : N ≤ Subgroup.centralizer {δ} := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh, mulAut_mul_conj, hδJ j (Subgroup.mem_subgroupOf.1 hj)]
  have hΓC : Γ ≤ C := fun g hg => (mem_entrywiseFixedGroup.1 hg).1
  have hmemΓ : ∀ g : C, g ∈ Γ.subgroupOf C ↔ δ g = g := fun g => by
    rw [Subgroup.mem_subgroupOf, mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext ((coe_entrywiseAdjointAut τ σ g).trans h)
    · intro h
      exact ⟨g.2, (coe_entrywiseAdjointAut τ σ g).symm.trans (congrArg Subtype.val h)⟩
  have hJΓC : J.subgroupOf C = ⁅Γ.subgroupOf C, Γ.subgroupOf C⁆ := by
    have h1 : ⁅Γ.subgroupOf C, Γ.subgroupOf C⁆.map C.subtype = J := by
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hΓC, hΓ']
    rw [← h1, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
  have hpres : ∀ β ∈ Subgroup.centralizer {δ}, ∀ j : C, j ∈ J.subgroupOf C →
      β j ∈ J.subgroupOf C := by
    intro β hβ j hj
    have hβδ : δ * β = β * δ := Subgroup.mem_centralizer_iff.1 hβ δ (Set.mem_singleton δ)
    have hΓβ : (Γ.subgroupOf C).map β.toMonoidHom ≤ Γ.subgroupOf C := by
      rintro _ ⟨g, hg, rfl⟩
      refine (hmemΓ _).2 ?_
      change (δ * β) g = β g
      rw [hβδ, MulAut.mul_apply, (hmemΓ g).1 hg]
    rw [hJΓC] at hj ⊢
    have h2 : ⁅Γ.subgroupOf C, Γ.subgroupOf C⁆.map β.toMonoidHom ≤
        ⁅Γ.subgroupOf C, Γ.subgroupOf C⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hΓβ hΓβ
    exact h2 ⟨j, hj, rfl⟩
  have hnormal : (N.subgroupOf (Subgroup.centralizer {δ})).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨j, hj, hjn⟩ := Subgroup.mem_subgroupOf.1 hn
    refine Subgroup.mem_subgroupOf.2 ⟨(g : MulAut C) j, hpres g g.2 j hj, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hjn]
    exact (mulAut_mul_conj_mul_inv _ _).symm
  have hcent : Subgroup.centralizer {δ} ⊓ Subgroup.centralizer (N : Set (MulAut C)) =
      Subgroup.zpowers δ := by
    refine le_antisymm (fun β hβ => ?_) ?_
    · obtain ⟨-, hβN⟩ := Subgroup.mem_inf.1 hβ
      have hfix : ∀ j : C, (j : ModGL τ K) ∈ J → β j = j := by
        intro j hj
        have hn : MulAut.conj j ∈ N := ⟨j, Subgroup.mem_subgroupOf.2 hj, rfl⟩
        have h1 : MulAut.conj j * β = β * MulAut.conj j :=
          Subgroup.mem_centralizer_iff.1 hβN _ hn
        have h2 : MulAut.conj (β j) = MulAut.conj j := by
          rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
        exact hinj h2
      obtain ⟨η, hηk, rfl⟩ := hfixer β hfix
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_fixed hηk)
      refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
      rw [hδ]
      exact (map_zpow (entrywiseAdjointAutHom (τ := τ)) σ n).symm
    · refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
        fun h hh => by rw [Set.mem_singleton_iff.1 hh], Subgroup.mem_centralizer_iff.2
          fun n hn => (Subgroup.mem_centralizer_iff.1 (hNδ hn) δ (Set.mem_singleton δ)).symm⟩)
  exact ⟨hJC, eJ.isSimpleGroup, not_commute_fixedFieldImage τ.rank_pos σ,
    ⟨(J.subgroupOf C).equivMapOfInjective _ hinj⟩, hNδ, hnormal, hcent⟩

theorem eq_of_ne_one_of_card_le_two {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q ≤ 2)
    {a b : Q} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have : Fintype Q := Fintype.ofFinite Q
  have h3 : ({1, a, b} : Finset Q).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb]), Finset.card_pair hab]
  have h4 := Finset.card_le_univ ({1, a, b} : Finset Q)
  rw [h3, ← Nat.card_eq_fintype_card] at h4
  omega

theorem mem_inner_of_pow_mul_eq_one {C : Type*} [Group C] [Finite C]
    {D : Subgroup (MulAut C)} [D.Normal]
    (hidx : ((CFSG.ComponentClassification.OuterAutomorphisms.inner C).subgroupOf D).index ∣ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d γ : MulAut C} (hd : d ∈ D) (hγ : γ ^ p = 1)
    (hdγ : (d * γ) ^ p = 1) : d ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner C := by
  classical
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner C with hI
  have : Finite (MulAut C) := MulEquiv.finite_left
  set q := QuotientGroup.mk' (I.subgroupOf D) with hq
  have hQcard : Nat.card (D ⧸ I.subgroupOf D) ≤ 2 := by
    rw [← Subgroup.index_eq_card]
    exact Nat.le_of_dvd two_pos hidx
  have hγD : γ * d * γ⁻¹ ∈ D := Subgroup.Normal.conj_mem ‹D.Normal› d hd γ
  have hqeq : q ⟨d, hd⟩ = q ⟨γ * d * γ⁻¹, hγD⟩ := by
    by_cases hdI : d ∈ I
    · have h1 : q ⟨d, hd⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hdI
      have h2 : q ⟨γ * d * γ⁻¹, hγD⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.Normal.conj_mem inferInstance d hdI γ)
      rw [h1, h2]
    · refine eq_of_ne_one_of_card_le_two hQcard ?_ ?_
      · exact fun h => hdI ((QuotientGroup.eq_one_iff (N := I.subgroupOf D) (⟨d, hd⟩ : D)).1 h)
      · intro h
        have h1 : γ * d * γ⁻¹ ∈ I :=
          (QuotientGroup.eq_one_iff (N := I.subgroupOf D) (⟨γ * d * γ⁻¹, hγD⟩ : D)).1 h
        have h2 := Subgroup.Normal.conj_mem inferInstance _ h1 γ⁻¹
        rw [show γ⁻¹ * (γ * d * γ⁻¹) * γ⁻¹⁻¹ = d by group] at h2
        exact hdI h2
  set o := QuotientGroup.mk' I with ho
  have hcomm : Commute (o d) (o γ) := by
    have h1 : d⁻¹ * (γ * d * γ⁻¹) ∈ I := by
      have := (QuotientGroup.eq (s := I.subgroupOf D)).1 hqeq
      exact this
    have h2 := Subgroup.Normal.conj_mem inferInstance _ h1 γ⁻¹
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    convert h2 using 1
    group
  have hp1 : o d ^ p = 1 := by
    have h1 : (o d * o γ) ^ p = 1 := by rw [← map_mul, ← map_pow, hdγ, map_one]
    rwa [hcomm.mul_pow, ← map_pow o γ, hγ, map_one, mul_one] at h1
  have hq2 : q ⟨d, hd⟩ ^ 2 = 1 := by
    have h1 := orderOf_dvd_natCard (q ⟨d, hd⟩)
    rw [← Subgroup.index_eq_card] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 (h1.trans hidx)
  have h21 : o d ^ 2 = 1 := by
    have h1 : (⟨d, hd⟩ : D) ^ 2 ∈ I.subgroupOf D := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
      exact hq2
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h1
  have hord : orderOf (o d) ∣ Nat.gcd p 2 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp1) (orderOf_dvd_of_pow_eq_one h21)
  rw [(Nat.coprime_primes hp Nat.prime_two).2 hp2] at hord
  have h1 : o d = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord)
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

theorem odd_E7_noninner_odd_prime_field_descent_and_local_core_trivial {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (B : Subgroup (MulAut (adjointGroup .E7 K)))
    (hB : (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range ≤ B) (α : B)
    (hα : (α : MulAut (adjointGroup .E7 K)) ∉
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range)
    (hαp : orderOf α = p) :
    p ∣ f ∧
    (∃ (σ : K ≃+* K) (δ : MulAut (adjointGroup .E7 K)), orderOf σ = p ∧
      δ * (α : MulAut (adjointGroup .E7 K)) * δ⁻¹ = entrywiseAdjointAut .E7 σ) ∧
    aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨-, -, -, -, ρ, -, -, -, hDnormal, hidx, hNF, -, ⟨π, -, -, hπ⟩, hfixer⟩ :=
    CFSG.RankThree.OddE7Rational.odd_E7_rational_inner_diagonal_field_automorphism_structure hℓ
      hℓ2 hf K hK (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f)
      (fun c => by rw [iterateFrobenius_def, hK]) _ _ rfl rfl
  have hα'p : orderOf (α : MulAut (adjointGroup .E7 K)) = p := by
    rw [Subgroup.orderOf_coe, hαp]
  have hαpow : (α : MulAut (adjointGroup .E7 K)) ^ p = 1 := by
    rw [← hα'p]
    exact pow_orderOf_eq_one _
  obtain ⟨⟨z, σ⟩, hzσ, -⟩ := hNF α
  simp only at hzσ
  have hσp1 : σ ^ p = 1 := by
    have h1 := congrArg π hαpow
    rw [map_pow, hzσ, hπ, map_one] at h1
    exact h1
  have hzinn := mem_inner_of_pow_mul_eq_one hidx hp hp2 ⟨z, rfl⟩
    (by rw [← entrywiseAdjointAut_pow, hσp1, entrywiseAdjointAut_one]) (hzσ ▸ hαpow)
  obtain ⟨x, hx⟩ : ρ z ∈ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range :=
    hzinn
  rw [← hx] at hzσ
  have hσp : orderOf σ = p := by
    refine orderOf_eq_prime hσp1 fun h => hα ?_
    rw [hzσ, h, entrywiseAdjointAut_one, mul_one]
    exact ⟨x, rfl⟩
  obtain ⟨hpf, δ, hδ⟩ := exists_conj_eq_entrywiseAdjointAut_of_orderOf .E7 hℓ hf K hK hp x σ hσp
    (by rw [← hzσ]; exact hα'p)
  rw [← hzσ] at hδ
  refine ⟨hpf, ⟨σ, δ, hσp, hδ⟩, ?_⟩
  have hfixer' : ∀ β : MulAut (adjointGroup .E7 K),
      (∀ j : adjointGroup .E7 K, (j : ModGL .E7 K) ∈ fixedFieldImage .E7 σ → β j = j) →
        ∃ η : K ≃+* K, (∀ c, σ c = c → η c = c) ∧ β = entrywiseAdjointAut .E7 η := by
    intro β hβ
    have hS := (hfixer (fixSubfield σ) _ rfl).1
    have hβS : β ∈ ((fixingSubgroup (MulAut (adjointGroup Tag.E7 K))
        {j : adjointGroup Tag.E7 K | (j : ModGL Tag.E7 K) ∈
          (adjointGroup Tag.E7 (fixSubfield σ)).map (baseChangeGL (fixSubfield σ).subtype)} :
            Subgroup (MulAut (adjointGroup Tag.E7 K))) : Set (MulAut (adjointGroup Tag.E7 K))) :=
      (mem_fixingSubgroup_iff _).2 fun j hj => hβ j hj
    rw [hS] at hβS
    obtain ⟨σ', rfl⟩ := hβS
    refine ⟨σ'.toRingEquiv, fun c hc => ?_, rfl⟩
    have h1 := σ'.commutes (⟨c, hc⟩ : fixSubfield σ)
    exact h1
  obtain ⟨hJC, hsimple, hnc, ⟨ι⟩, hNδ, hnormal, hcent⟩ :=
    odd_entrywise_canonical_core_data_of_fixer (τ := .E7) hℓ2 σ hfixer'
  exact aschbacherSolvableCore_centralizer_eq_bot_of_inner hp hJC hB α hαp δ _ hδ hsimple hnc ι
    hNδ hnormal hcent

end CFSG.RankThree.Chevalley
