module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Derived

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggRCS_eq_one_of_mem_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) {y : G} (hy : y ∈ Q) (hyp : y ^ p = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨y, hy⟩
  have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h1 : orderOf y ∣ Nat.gcd (2 ^ k) p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hyp)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

omit [Finite G] in
theorem ggRCS_pCore_le_of_sThree {X Q : Subgroup G} [hQn : (Q.subgroupOf X).Normal]
    (e : ↥X ⧸ Q.subgroupOf X ≃* Equiv.Perm (Fin 3)) :
    CFSG.Assembly.pCore 2 ↥X ≤ Q.subgroupOf X := by
  set φ : ↥X →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' (Q.subgroupOf X))
    with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφker : φ.ker = Q.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hPn : (CFSG.Assembly.pCore 2 ↥X).Normal :=
    Dichotomy.CentralizerContainment.pCore_normal_assembly 2 ↥X
  have hTn : ((CFSG.Assembly.pCore 2 ↥X).map φ).Normal := hPn.map φ hφs
  have hT2 : IsPGroup 2 ((CFSG.Assembly.pCore 2 ↥X).map φ) :=
    (Dichotomy.CentralizerContainment.pCore_isPGroup_assembly 2 ↥X).map φ
  have hT : (CFSG.Assembly.pCore 2 ↥X).map φ = ⊥ :=
    ggRCSS_perm_three_normal_two ((CFSG.Assembly.pCore 2 ↥X).map φ) hTn hT2
  rw [← hφker, ← Subgroup.map_eq_bot_iff]
  exact hT

omit [Finite G] in
theorem ggRCS_pCoreOf_eq_of_sThree {X Q : Subgroup G} (hQX : Q ≤ X) (hQ2 : IsPGroup 2 Q)
    [hQn : (Q.subgroupOf X).Normal] (e : ↥X ⧸ Q.subgroupOf X ≃* Equiv.Perm (Fin 3)) :
    CFSG.Assembly.pCoreOf 2 X = Q := by
  have hQ2X : IsPGroup 2 (Q.subgroupOf X) := hQ2.comap_of_injective X.subtype X.subtype_injective
  have h1 : Q.subgroupOf X ≤ CFSG.Assembly.pCore 2 ↥X :=
    Dichotomy.CentralizerContainment.le_pCore_assembly hQn hQ2X
  have h2 := ggRCS_pCore_le_of_sThree e
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (h2 hx)
  · intro q hq
    exact ⟨⟨q, hQX hq⟩, h1 (Subgroup.mem_subgroupOf.mpr hq), rfl⟩

theorem ggRCSLayer_of_derivedAt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G₀ M : Subgroup G}
    (hG₀M : G₀ ≤ M) (hM : M ≤ Subgroup.normalizer (G₀ : Set G)) {r : G}
    (h : GGRootCentDerivedAt p G₀ r) : GGRCSLayer p G₀ M r := by
  set X := ggRCSX G₀ r with hX
  set V := M ⊓ Subgroup.centralizer ({r} : Set G) with hV
  have hXV : X ≤ V := (ggOTwoPrime_le _).trans (inf_le_inf_right _ hG₀M)
  have hVX : V ≤ Subgroup.normalizer (X : Set G) := fun c hc =>
    ggMem_normalizer_oTwoPrime_inf_centralizer (hM hc.1) hc.2
  have hVXd : V ≤ Subgroup.normalizer (ggRCSXd G₀ r : Set G) :=
    hVX.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore X)
  have hXdV : ggRCSXd G₀ r ≤ V := (CFSG.Quasithin.perfectCore_le X).trans hXV
  have hperf : ⁅ggRCSXd G₀ r, ggRCSXd G₀ r⁆ = ggRCSXd G₀ r :=
    CFSG.Quasithin.perfectCore_perfect _
  rcases h with h1 | ⟨hpXd, ⟨Q₁, hQ₁, hQ₁2, hQ₁n, hq⟩, hcov⟩ | ⟨Q₁, hQ₁, hQ₁2, hQ₁n, he⟩
  ·
    refine ⟨∅, fun S hS => hS.elim, fun y hy hyp => ?_⟩
    rw [h1 y hy hyp]
    exact one_mem _
  ·
    refine ⟨{ggRCSXd G₀ r}, ?_, fun y hy hyp => ?_⟩
    · rintro S rfl
      left
      refine ⟨CFSG.Assembly.pCoreOf 2 (ggRCSXd G₀ r), hXdV, ?_, hperf, hpXd,
        Subgroup.map_subtype_le _, ggIsPGroup_pCoreOf 2 _,
        hVXd.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _), ?_⟩
      · exact ggIsSubnormal_of_normal hXdV
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hXdV).mpr hVXd)
      · intro _
        exact ggRCS_quasisimple_pCoreOf hp hp2 hQ₁2 (@hq hQ₁n) hpXd
    · rw [sSup_singleton]
      exact hcov y hy hyp
  ·
    obtain ⟨e⟩ := @he hQ₁n
    have hQ : CFSG.Assembly.pCoreOf 2 X = Q₁ := ggRCS_pCoreOf_eq_of_sThree hQ₁ hQ₁2 e
    have hVQ : V ≤ Subgroup.normalizer (Q₁ : Set G) := by
      rw [← hQ]
      exact hVX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    set f : ↥X →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' (Q₁.subgroupOf X))
      with hf
    have hfs : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hfker : f.ker = Q₁.subgroupOf X := by
      ext x
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    by_cases hp3 : p = 3
    · subst hp3
      set S := ((alternatingGroup (Fin 3)).comap f).map X.subtype with hS
      have hSX : S ≤ X := Subgroup.map_subtype_le _
      refine ⟨{S}, ?_, fun y hy hyp => ?_⟩
      · rintro S' rfl
        right
        refine ⟨rfl, X, Q₁, hSX, hXV, hVX, ?_, hQ₁2, hVQ, ?_, ?_⟩
        · intro q hq
          refine ⟨⟨q, hQ₁ hq⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_comap]
          have : f ⟨q, hQ₁ hq⟩ = 1 := by
            rw [← MonoidHom.mem_ker, hfker]
            exact hq
          rw [this]
          exact one_mem _
        · have h1 : Nat.card S = Nat.card ((alternatingGroup (Fin 3)).comap f) :=
            Nat.card_congr (Subgroup.equivMapOfInjective _ _ X.subtype_injective).symm.toEquiv
          rw [h1, ggRCSS_card_comap_of_surjective f hfs, ggRCSS_card_alternating_three, hfker]
          congr 1
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₁).toEquiv
        · intro _
          exact ⟨(QuotientGroup.quotientMulEquivOfEq rfl).trans e⟩
      · rw [sSup_singleton]
        refine ⟨⟨y, hy⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup]
        refine ggRCSS_sign_of_pow_three _ ?_
        rw [← map_pow]
        have : (⟨y, hy⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hyp)
        rw [this, map_one]
    · refine ⟨∅, fun S hS => hS.elim, fun y hy hyp => ?_⟩
      have hfy : f ⟨y, hy⟩ = 1 := by
        have h1 : (f ⟨y, hy⟩) ^ p = 1 := by
          rw [← map_pow]
          have : (⟨y, hy⟩ : ↥X) ^ p = 1 := Subtype.ext (by simpa using hyp)
          rw [this, map_one]
        have h6 : (f ⟨y, hy⟩) ^ 6 = 1 := by
          have := pow_card_eq_one (G := Equiv.Perm (Fin 3)) (x := f ⟨y, hy⟩)
          simpa [Fintype.card_perm, Nat.factorial] using this
        have hcop : Nat.Coprime p 6 := by
          rw [show (6 : ℕ) = 2 * 3 by norm_num]
          refine Nat.Coprime.mul_right ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
            ((Nat.coprime_primes hp Nat.prime_three).mpr hp3)
        have h2 : orderOf (f ⟨y, hy⟩) ∣ Nat.gcd p 6 :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h6)
        rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h2
        exact h2
      have hyQ : y ∈ Q₁ := by
        have : (⟨y, hy⟩ : ↥X) ∈ f.ker := hfy
        rw [hfker, Subgroup.mem_subgroupOf] at this
        exact this
      rw [ggRCS_eq_one_of_mem_two hp hp2 hQ₁2 hyQ hyp]
      exact one_mem _

omit [Finite G] in
theorem ggRCS_eq_one_of_not_dvd {p : ℕ} (hp : p.Prime) {X : Subgroup G} [Finite X]
    (hpX : ¬ p ∣ Nat.card X) {y : G} (hy : y ∈ X) (hyp : y ^ p = 1) : y = 1 := by
  have h1 : orderOf (⟨y, hy⟩ : ↥X) ∣ Nat.card X := orderOf_dvd_natCard _
  have h2 : orderOf (⟨y, hy⟩ : ↥X) ∣ p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_dvd_of_pow_eq_one hyp
  have hcop : Nat.Coprime p (Nat.card X) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpX
  have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1
  rw [orderOf_eq_one_iff] at h3
  exact congrArg Subtype.val h3

theorem ggRootCentDerivedAt_of_perfect {p : ℕ} (hp : p.Prime) {G₀ : Subgroup G} {r : G}
    (hperf : ⁅ggRCSX G₀ r, ggRCSX G₀ r⁆ = ggRCSX G₀ r) {Q : Subgroup G}
    (hQX : Q ≤ ggRCSX G₀ r) (hQ2 : IsPGroup 2 Q) [hQn : (Q.subgroupOf (ggRCSX G₀ r)).Normal]
    (hq : p ∣ Nat.card (ggRCSX G₀ r) →
      CFSG.IsQuasisimple (↥(ggRCSX G₀ r) ⧸ Q.subgroupOf (ggRCSX G₀ r))) :
    GGRootCentDerivedAt p G₀ r := by
  have hc : ggRCSXd G₀ r = ggRCSX G₀ r := CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf
  by_cases hpX : p ∣ Nat.card (ggRCSX G₀ r)
  · refine Or.inr (Or.inl ?_)
    rw [hc]
    refine ⟨hpX, ⟨Q, hQX, hQ2, hQn, ?_⟩, fun y hy _ => hy⟩
    intro _
    exact hq hpX
  · exact Or.inl fun y hy hyp => ggRCS_eq_one_of_not_dvd hp hpX hy hyp

end Derived

end CFSG.StandardType
