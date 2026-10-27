module

public import CFSG.RankThree.PartOne.KF.F122ExcEngine
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityCommutingSL2
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityTransposition
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent
public import CFSG.RankThree.PartOne.KF.F122Sp
public import CFSG.RankThree.PartOne.S11c.Sec66Exc
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartTwo.Census (localRank_eq_of_mulEquiv)
open scoped MatrixGroups

theorem card_fixSubfield_cube_row {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (fixSubfield σ) = ℓ ^ f := by
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 3 * f) hK3
  have hσfr : σ = fr ^ f := RingEquiv.ext fun c => by
    rw [hσ, ringAut_pow_apply_of_frobenius hfr f c]
  have hσo : orderOf σ = 3 := by
    rw [hσfr, orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro_left 3 rfl), hord,
      Nat.mul_div_cancel _ (by omega)]
  obtain ⟨-, hσcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ
    (by omega : 1 ≤ 3 * f) hK3 σ
  rw [hσo, Nat.mul_div_cancel_left _ (by norm_num)] at hσcard
  exact hσcard

theorem two_le_localRank_graphFixedD4
    {d : ℕ} (hd : 1 ≤ d) {k : Type} [Field k] [Finite k] (hk : Nat.card k = (2 ^ d) ^ 3)
    (σ₀ : k ≃+* k) (hσ₀ : (∀ c, σ₀ c = c ^ 2 ^ d) ∨ ∀ c, σ₀ c = c ^ (2 ^ d) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ 2 ^ d - 1) :
    2 ≤ localRank p ↥(graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have hq3 : ∀ c : k, c ^ (2 ^ d) ^ 3 = c := fun c => by
    rw [← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  obtain ⟨σ₁, hσ₁, ⟨e₁⟩⟩ : ∃ σ₁ : k ≃+* k, (∀ c, σ₁ c = c ^ 2 ^ d) ∧
      Nonempty (↥(graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 k σ₁.toRingHom)) := by
    rcases hσ₀ with h | h
    · exact ⟨σ₀, h, ⟨MulEquiv.refl _⟩⟩
    · refine ⟨σ₀.symm, fun c => ?_, ?_⟩
      · refine σ₀.symm_apply_eq.2 ?_
        rw [h, ← pow_mul, show 2 ^ d * (2 ^ d) ^ 2 = (2 ^ d) ^ 3 by ring, hq3]
      · obtain ⟨f, -⟩ := exists_mulEquiv_of_map_eq (trialityTranspositionAut k)
          (map_trialityTranspositionAut_graphFixedRootGroup σ₀)
        exact ⟨f⟩
  rw [localRank_eq_of_mulEquiv e₁ hp]
  have hσ₁3 : σ₁ ^ 3 = 1 := RingEquiv.ext fun c => by
    rw [ringEquiv_pow_three_apply, hσ₁, hσ₁, hσ₁, ← pow_mul, ← pow_mul,
      show 2 ^ d * (2 ^ d * 2 ^ d) = (2 ^ d) ^ 3 by ring, hq3]
    rfl
  obtain ⟨ι, η, hι, hη, hcomm⟩ :=
    CFSG.RankThree.Chevalley.triality_D4_commuting_faithful_extension_and_fixed_SL2 k σ₁ hσ₁3
  have hkcard : Nat.card (fixSubfield σ₁) = 2 ^ d :=
    card_fixSubfield_cube_row Nat.prime_two hd hk σ₁ hσ₁
  have : Finite (fixSubfield σ₁) := Subtype.finite
  have : Fintype (fixSubfield σ₁) := Fintype.ofFinite _
  have : CharP (fixSubfield σ₁) 2 :=
    charP_of_card_eq_prime_pow (f := d) (by rw [← Nat.card_eq_fintype_card, hkcard])
  let φ₀ : SL(2, fixSubfield σ₁) →* ↥(graphFixedRootGroup TwistTag.D4 k σ₁.toRingHom) :=
    ι.comp (Matrix.SpecialLinearGroup.map (fixSubfield σ₁).subtype)
  have hφ₀ : Function.Injective φ₀ := by
    refine hι.comp fun A B hAB => ?_
    apply Subtype.ext
    exact Matrix.map_injective Subtype.val_injective (congrArg Subtype.val hAB)
  let φ : Fin 2 → SL(2, fixSubfield σ₁) →* ↥(graphFixedRootGroup TwistTag.D4 k σ₁.toRingHom) :=
    ![φ₀, η]
  have hφ : ∀ i, Function.Injective (φ i) := by
    intro i
    fin_cases i
    · exact hφ₀
    · exact hη
  have hcom : ∀ i j : Fin 2, i ≠ j → ∀ A B : SL(2, fixSubfield σ₁), φ i A * φ j B = φ j B * φ i A := by
    intro i j hij A B
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hcomm _ _
    · exact (hcomm _ _).symm
    · exact absurd rfl hij
  exact CFSG.RankThree.PartTwo.Census.Exceptional.le_localRank_of_commuting_SL2_even
    (ringChar.eq (fixSubfield σ₁) 2) hp hp2 (by rwa [← Nat.card_eq_fintype_card, hkcard])
    (by norm_num) φ hφ hcom

theorem kf122Row3_holds
    : KF122Row 3 := by
  intro G _ _ p L hp hp5 hmodel _ α hαp hαinn hLRA
  obtain ⟨f, hf, hpq, hM⟩ := hmodel
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hCEM⟩ := lieModel_trialityD4_iff.mp hM
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hCEM.2
  have hK : Nat.card K = (2 ^ f) ^ 3 := hKcard
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv _ e.toEquiv
  have hα1 : α ≠ 1 := fun h => hαinn (h ▸ Subgroup.one_mem _)
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  set α' : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := MulAut.congr e α
  have hα'ord : orderOf α' = p := (orderOf_congr e α).trans hord
  have hα'inn : α' ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  obtain ⟨-, -, ⟨Θ, hΘ, -⟩, hcyc, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ hσ
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial Nat.prime_two hf K hK σ hσ
      Θ hΘ hp (by omega) ⊤ le_top ⟨α', Subgroup.mem_top _⟩ hα'inn
      (by rw [Subgroup.orderOf_mk]; exact hα'ord)
  obtain ⟨f', hff'⟩ := hpf
  have hd : 1 ≤ f' := one_le_of_mul_eq hf hff'
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨φ, hφ, hφord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 3 * f) hK3
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ 2 ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega) (by rw [hφord, hff']; exact ⟨p, by ring⟩),
      hφord, hff', show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers (Θ α') = Subgroup.zpowers δc := by
    have h1 : Nat.card (Subgroup.zpowers (Θ α')) = p := by rw [Nat.card_zpowers]; exact hηord
    have h2 : Nat.card (Subgroup.zpowers δc) = p := by rw [Nat.card_zpowers, hδcord]
    have : Finite (Subgroup.zpowers (Θ α')) :=
      Nat.finite_of_card_ne_zero (by rw [h1]; exact hp.ne_zero)
    have : Finite (Subgroup.zpowers δc) :=
      Nat.finite_of_card_ne_zero (by rw [h2]; exact hp.ne_zero)
    exact IsCyclic.subgroup_eq_iff_card_eq.mpr (h1.trans h2.symm)
  have hfix_eq : fixSub (MulAut.conj h₀ * MulAut.congr e α * (MulAut.conj h₀)⁻¹) =
      fixSub (fieldActor σ δc) := by
    have h1 : MulAut.conj h₀ * MulAut.congr e α * (MulAut.conj h₀)⁻¹ = fieldActor σ (Θ α') := hh₀
    rw [h1]
    apply fixSub_eq_of_zpowers_eq
    have h2 := congrArg (Subgroup.map (fieldActorHom (t := TwistTag.D4) σ)) hzp
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
    exact h2
  have hK' : Nat.card K = 2 ^ (3 * f' * p) := by rw [hK3, hff']; ring
  have hσ' : ∀ c, σ c = c ^ 2 ^ (f' * p) := fun c => by rw [hσ, hff', mul_comm]
  obtain ⟨-, -, hk, hres, -, -, hfixJ, hsimple, hnc, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel Nat.prime_two hd hp.two_le hm3
      K hK' σ hσ' δc hδc
  have : Finite (fixSubfield δc) := Subtype.finite
  have : Fintype (fixSubfield δc) := Fintype.ofFinite _
  set J := trialityFieldImage σ δc
  let e3 : ↥(fixSub (fieldActor σ δc)) ≃* ↥J :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  have hK0 : Nat.card (fixSubfield δc) = (2 ^ f') ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hcardK0 : Fintype.card (fixSubfield δc) = 2 ^ (3 * f') := by
    rw [← Nat.card_eq_fintype_card, hk]
  have hσ0pow : ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ 2 ^ (f' * p) := fun c =>
    Subtype.ext (by rw [hres c, hσ', SubmonoidClass.coe_pow])
  obtain ⟨j, r, hr, hpjr⟩ : ∃ j r : ℕ, (r = 1 ∨ r = 2) ∧ p = 3 * j + r := by
    have h3 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    rcases (show p % 3 = 1 ∨ p % 3 = 2 by omega) with h | h
    · exact ⟨p / 3, 1, Or.inl rfl, by omega⟩
    · exact ⟨p / 3, 2, Or.inr rfl, by omega⟩
  have hpowj : ∀ c : fixSubfield δc, c ^ (2 ^ (3 * f')) ^ j = c := fun c => by
    have h := FiniteField.pow_card_pow j c
    rwa [hcardK0] at h
  have hσ0pow' : ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ 2 ^ (f' * r) := fun c => by
    have h2 : 2 ^ (f' * p) = (2 ^ (3 * f')) ^ j * 2 ^ (f' * r) := by
      rw [hpjr]
      ring
    rw [hσ0pow c, h2, pow_mul, hpowj c]
  have hσ0orient : (∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ 2 ^ f') ∨
      ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ (2 ^ f') ^ 2 := by
    rcases hr with rfl | rfl
    · exact Or.inl fun c => by rw [hσ0pow' c, mul_one]
    · exact Or.inr fun c => by rw [hσ0pow' c, ← pow_mul]
  have hpd : p ∣ 2 ^ f' - 1 := dvd_two_pow_sub_one_of_mul hp (hff' ▸ hpq)
  have hlow := two_le_localRank_graphFixedD4 hd hK0 (fixSubfieldRestrict σ δc) hσ0orient hp
    (by omega) hpd
  let eJ' : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
      (fixSubfieldRestrict σ δc).toRingHom) ≃* ↥J :=
    (graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
        (fixSubfieldRestrict σ δc).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _)
  exact false_of_conj_fixed hp e hαp hαinn (MulAut.conj h₀) (fieldActor σ δc) hfix_eq
    (e3.trans eJ'.symm) hlow hLRA

end CFSG.RankThree.PartOne
