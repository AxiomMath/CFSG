module

public import CFSG.RankThree.Chevalley.SteinbergBTNoninnerLocalCore
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.LieType.Chevalley.OddPinnedComponents

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality
  finite_field_prime_power_characteristic)
open CFSG.ComponentClassification.UnbalancedCatalog (mem_zpowers_of_fixed)
open SteinbergBT (not_commute_fixedFieldImage)

variable {τ : Tag} {K : Type} [Field K]

theorem eq_of_conj_mul_entrywiseAdjointAut_eq
    (hNF : ∀ η : MulAut (adjointGroup τ K), ∃! gβ : adjointGroup τ K × (K ≃+* K),
      η = MulAut.conj gβ.1 * entrywiseAdjointAut τ gβ.2)
    {g g' : adjointGroup τ K} {β β' : K ≃+* K}
    (h : MulAut.conj g * entrywiseAdjointAut τ β = MulAut.conj g' * entrywiseAdjointAut τ β') :
    g = g' ∧ β = β' := by
  obtain ⟨_, -, huniq⟩ := hNF (MulAut.conj g * entrywiseAdjointAut τ β)
  exact Prod.ext_iff.1 ((huniq (g, β) rfl).trans (huniq (g', β') h).symm)

theorem conj_normalForm_of_pointwise
    (hNF : ∀ η : MulAut (adjointGroup τ K), ∃! gβ : adjointGroup τ K × (K ≃+* K),
      ∀ h : adjointGroup τ K, (η h : ModGL τ K) = (gβ.1 : ModGL τ K) *
        Units.map (entrywiseHom gβ.2.toRingHom) (h : ModGL τ K) * (gβ.1 : ModGL τ K)⁻¹)
    (η : MulAut (adjointGroup τ K)) : ∃! gβ : adjointGroup τ K × (K ≃+* K),
      η = MulAut.conj gβ.1 * entrywiseAdjointAut τ gβ.2 := by
  have hiff : ∀ gβ : adjointGroup τ K × (K ≃+* K),
      (∀ h : adjointGroup τ K, (η h : ModGL τ K) = (gβ.1 : ModGL τ K) *
        Units.map (entrywiseHom gβ.2.toRingHom) (h : ModGL τ K) * (gβ.1 : ModGL τ K)⁻¹) ↔
      η = MulAut.conj gβ.1 * entrywiseAdjointAut τ gβ.2 := fun gβ => by
    constructor
    · intro h
      refine MulEquiv.ext fun u => Subtype.ext ?_
      rw [h u, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_entrywiseAdjointAut, Subgroup.coe_inv]
    · rintro rfl u
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_entrywiseAdjointAut, Subgroup.coe_inv]
  obtain ⟨gβ, hgβ, huniq⟩ := hNF η
  exact ⟨gβ, (hiff gβ).1 hgβ, fun q hq => huniq q ((hiff q).2 hq)⟩

theorem exists_conj_eq_entrywiseAdjointAut_of_orderOf (τ : Tag) {ℓ f p : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (x : adjointGroup τ K) (σ : K ≃+* K) (hσp : orderOf σ = p)
    (hαp : orderOf (MulAut.conj x * entrywiseAdjointAut τ σ) = p) :
    p ∣ f ∧ ∃ δ : MulAut (adjointGroup τ K),
      δ * (MulAut.conj x * entrywiseAdjointAut τ σ) * δ⁻¹ = entrywiseAdjointAut τ σ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  set α := MulAut.conj x * entrywiseAdjointAut τ σ with hασ
  have hαpow : α ^ p = 1 := by rw [← hαp]; exact pow_orderOf_eq_one α
  obtain ⟨φ, hφ, hφord, hφgen, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hpf : p ∣ f := by
    rw [← hcard, ← hσp]
    exact orderOf_dvd_natCard σ
  set e := f / p with he
  have hep : e * p = f := Nat.div_mul_cancel hpf
  have he1 : 1 ≤ e := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hT : ∀ c, (φ ^ e) c = c ^ (ℓ ^ e) := by
    intro c
    rw [ringEquiv_pow_apply]
    have hit : ∀ n : ℕ, (⇑φ)^[n] c = c ^ (ℓ ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Function.iterate_succ_apply', ih, hφ, pow_succ, pow_mul]
    exact hit e
  have hσmem : σ ∈ Subgroup.zpowers φ := by rw [hφgen]; exact Subgroup.mem_top σ
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hσmem)
  replace hk : φ ^ k = σ := hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    rw [← hk, orderOf_one] at hσp
    exact hp.one_lt.ne hσp
  have hgcd : Nat.gcd f k = e := by
    have h1 := orderOf_pow' φ hk0
    rw [hk, hσp, hφord] at h1
    rw [he, h1, Nat.div_div_self (Nat.gcd_dvd_left f k) (by omega)]
  have hzp : Subgroup.zpowers σ = Subgroup.zpowers (φ ^ e) := by
    rw [← hk, ← zpow_natCast, ← zpow_natCast φ e, Subgroup.zpowers_eq_zpowers_iff', hφord,
      Int.gcd_natCast_natCast, Int.gcd_natCast_natCast, Nat.gcd_comm, hgcd,
      Nat.gcd_eq_left ⟨p, hep.symm⟩]
  have hTσ : φ ^ e ∈ Subgroup.zpowers σ := by rw [hzp]; exact Subgroup.mem_zpowers _
  have hσT : σ ∈ Subgroup.zpowers (φ ^ e) := by rw [← hzp]; exact Subgroup.mem_zpowers _
  obtain ⟨j', -, hj'⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hTσ)
  replace hj' : σ ^ j' = φ ^ e := hj'
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hσT)
  replace hj : (φ ^ e) ^ j = σ := hj
  have hjj : α ^ (j' * j) = α := by
    have h1 : σ ^ (j' * j) = σ ^ 1 := by rw [pow_mul, hj', hj, pow_one]
    rw [pow_eq_pow_iff_modEq, hσp] at h1
    have h2 : α ^ (j' * j) = α ^ 1 := by rw [pow_eq_pow_iff_modEq, hαp]; exact h1
    rwa [pow_one] at h2
  have hβ : α ^ j' = MulAut.conj (((List.range j').map fun i =>
      (entrywiseAdjointAut τ σ ^ i) x).prod) * entrywiseAdjointAut τ (φ ^ e) := by
    rw [hασ, conj_mul_pow, ← entrywiseAdjointAut_pow, hj']
  have hβp : (MulAut.conj (((List.range j').map fun i =>
      (entrywiseAdjointAut τ σ ^ i) x).prod) * entrywiseAdjointAut τ (φ ^ e)) ^ p = 1 := by
    rw [← hβ, ← pow_mul, mul_comm, pow_mul, hαpow, one_pow]
  obtain ⟨δ, hδ⟩ := exists_conj_eq_entrywiseAdjointAut τ K hK he1 hp.one_lt.le hep (φ ^ e) hT
    (AlgebraicClosure K) _ hβp
  refine ⟨hpf, δ, ?_⟩
  have hαβ : α = (α ^ j') ^ j := by rw [← pow_mul, hjj]
  rw [hαβ, ← conj_pow, hβ, hδ, ← entrywiseAdjointAut_pow, hj]

theorem odd_entrywise_canonical_core_data {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) [Finite K]
    [CharP K ℓ]
    (hNF : ∀ η : MulAut (adjointGroup τ K), ∃ gβ : adjointGroup τ K × (K ≃+* K),
      η = MulAut.conj gβ.1 * entrywiseAdjointAut τ gβ.2) (σ : K ≃+* K) :
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
  set ι : ZMod ℓ →+* K := ZMod.castHom (dvd_refl ℓ) K
  set ιk : ZMod ℓ →+* fixSubfield σ := ZMod.castHom (dvd_refl ℓ) (fixSubfield σ)
  have hιk : ι = (fixSubfield σ).subtype.comp ιk := RingHom.ext_zmod _ _
  have hHJ : ∀ g0 ∈ adjointGroup τ (ZMod ℓ), baseChangeGL ι g0 ∈ J := fun g0 hg0 =>
    ⟨baseChangeGL ιk g0, baseChangeGL_mem_adjointGroup ιk hg0, by
      rw [baseChangeGL_baseChangeGL, ← hιk]⟩
  have hodd : Odd (Nat.card (ZMod ℓ)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2
  have hfaith := (exceptional_Lang_finite_root_centralizer_faithfulness τ (ZMod ℓ) hodd K ι).2.2.1
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
      obtain ⟨⟨g, η⟩, hgη⟩ := hNF β
      simp only at hgη
      have hg1 : g = 1 := by
        refine Subtype.ext (hfaith g g.2 fun h hh => ?_)
        obtain ⟨g0, hg0, rfl⟩ := hh
        have hhJ := hHJ g0 hg0
        have h1 := congrArg Subtype.val (hfix ⟨_, hJC hhJ⟩ hhJ)
        rw [hgη, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          coe_entrywiseAdjointAut, Subgroup.coe_inv] at h1
        change (g : ModGL τ K) * Units.map (entrywiseHom η.toRingHom) (baseChangeGL ι g0) *
          (g : ModGL τ K)⁻¹ = baseChangeGL ι g0 at h1
        rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
          RingHom.ext_zmod (η.toRingHom.comp ι) ι] at h1
        exact mul_inv_eq_iff_eq_mul.1 h1
      subst hg1
      have hβη : β = entrywiseAdjointAut τ η := by rw [hgη, map_one, one_mul]
      have hηk : ∀ c, σ c = c → η c = c := fun c hc => by
        have h1 := hfix (adjX τ K ⟨0, τ.rank_pos⟩ c) (xUnit_mem_fixedFieldImage _ hc)
        rw [hβη, FieldGraphFieldPointwise.entrywiseAdjointAut_adjX] at h1
        exact adjX_injective _ h1
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_fixed hηk)
      refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
      rw [hβη, hδ]
      exact (map_zpow (entrywiseAdjointAutHom (τ := τ)) σ n).symm
    · refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
        fun h hh => by rw [Set.mem_singleton_iff.1 hh], Subgroup.mem_centralizer_iff.2
          fun n hn => (Subgroup.mem_centralizer_iff.1 (hNδ hn) δ (Set.mem_singleton δ)).symm⟩)
  exact ⟨hJC, eJ.isSimpleGroup, not_commute_fixedFieldImage τ.rank_pos σ,
    ⟨(J.subgroupOf C).equivMapOfInjective _ hinj⟩, hNδ, hnormal, hcent⟩

theorem odd_Chevalley_inner_field_noninner_prime_local_core_trivial (τ : Tag) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    (hNF : ∀ η : MulAut (adjointGroup τ K), ∃! gβ : adjointGroup τ K × (K ≃+* K),
      η = MulAut.conj gβ.1 * entrywiseAdjointAut τ gβ.2)
    {p : ℕ} (hp : p.Prime) (B : Subgroup (MulAut (adjointGroup τ K)))
    (hB : (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range ≤ B) (α : B)
    (hα : (α : MulAut (adjointGroup τ K)) ∉
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range)
    (hαp : orderOf α = p) (x : adjointGroup τ K) (σ : K ≃+* K)
    (hxσ : (α : MulAut (adjointGroup τ K)) = MulAut.conj x * entrywiseAdjointAut τ σ) :
    orderOf σ = p ∧ p ∣ f ∧
      (∃ δ : MulAut (adjointGroup τ K),
        δ * (α : MulAut (adjointGroup τ K)) * δ⁻¹ = entrywiseAdjointAut τ σ) ∧
      aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL τ K) := finite_modGL
  have hα'p : orderOf (α : MulAut (adjointGroup τ K)) = p := by rw [Subgroup.orderOf_coe, hαp]
  have hσp : orderOf σ = p := by
    have hpow : (α : MulAut (adjointGroup τ K)) ^ p = 1 := by
      rw [← hα'p]
      exact pow_orderOf_eq_one _
    rw [hxσ, conj_mul_pow, ← entrywiseAdjointAut_pow] at hpow
    have h1 : MulAut.conj (((List.range p).map fun i => (entrywiseAdjointAut τ σ ^ i) x).prod) *
        entrywiseAdjointAut τ (σ ^ p) = MulAut.conj 1 * entrywiseAdjointAut τ 1 := by
      rw [hpow, map_one, entrywiseAdjointAut_one, one_mul]
    have hσ1 : σ ≠ 1 := fun h => hα (by
      rw [hxσ, h, entrywiseAdjointAut_one, mul_one]
      exact ⟨x, rfl⟩)
    exact orderOf_eq_prime (eq_of_conj_mul_entrywiseAdjointAut_eq hNF h1).2 hσ1
  obtain ⟨hpf, δ, hδ⟩ := exists_conj_eq_entrywiseAdjointAut_of_orderOf τ hℓ hf K hK hp x σ hσp
    (by rw [← hxσ]; exact hα'p)
  rw [← hxσ] at hδ
  obtain ⟨hJC, hsimple, hnc, ⟨ι⟩, hNδ, hnormal, hcent⟩ :=
    odd_entrywise_canonical_core_data hℓ2 (fun η => (hNF η).exists) σ
  exact ⟨hσp, hpf, ⟨δ, hδ⟩, aschbacherSolvableCore_centralizer_eq_bot_of_inner hp hJC hB α hαp
    δ _ hδ hsimple hnc ι hNδ hnormal hcent⟩

end CFSG.RankThree.Chevalley
