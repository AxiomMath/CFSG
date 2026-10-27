module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcD4
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcE2
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcD4Sing
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcD4E2QPlus
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient
import CFSG.Quasithin.EmptyFaithful.R3c18G

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

open CFSG.RankThree.PartTwo.Sec13.KF135Proof CFSG.LieType.SeitzGeneration
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
  (exists_mulEquiv_graphFixedRootGroup_frobenius_sq_D4)


theorem exists_singular_D4 {k : Type} [Field k] [Finite k] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = (2 ^ f) ^ 3) (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (h6 : p ∣ (2 ^ f) ^ 6 - 1) (h1 : ¬ p ∣ 2 ^ f - 1)
    (A : Subgroup ↥(graphFixedRootGroup TwistTag.D4 k σ.toRingHom))
    (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) :
    ∃ b ∈ A, b ≠ 1 ∧ ∃ w : ↥(graphFixedRootGroup TwistTag.D4 k σ.toRingHom),
      w ≠ 1 ∧ w ^ 2 = 1 ∧ b * w = w * b := by
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hqq : 2 ^ f ≤ (2 ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  rw [pow_six_sub_one_eq hq1] at h6
  rcases (Nat.Prime.dvd_mul hp).mp h6 with h6 | h6
  · rcases (Nat.Prime.dvd_mul hp).mp h6 with h6 | h6
    · exact absurd h6 h1
    · exact exists_singular_D4_qplus hf hk σ hσ hp (by omega) h6 hA hAc
  · rcases (Nat.Prime.dvd_mul hp).mp h6 with h6 | h6
    · refine exists_singular_D4_threeSix hf hk σ hσ (ε := 1) (Or.inl rfl) hp (by omega) ?_ hA
        hAc
      rw [one_mul]
      exact_mod_cast h6
    · refine exists_singular_D4_threeSix hf hk σ hσ (ε := -1) (Or.inr rfl) hp (by omega) ?_ hA
        hAc
      have h' : ((p : ℕ) : ℤ) ∣ (((2 ^ f) ^ 2 - 2 ^ f + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 h6
      rw [Nat.cast_add, Nat.cast_sub hqq, Nat.cast_one] at h'
      have e : ((2 ^ f : ℕ) : ℤ) ^ 2 + -1 * ((2 ^ f : ℕ) : ℤ) + 1 =
          (((2 ^ f) ^ 2 : ℕ) : ℤ) - ((2 ^ f : ℕ) : ℤ) + 1 := by
        push_cast
        ring
      rw [e]
      exact h'

theorem false_of_kF135Hyp_D4_E2 {S : Type} [Group S] [Finite S] {p : ℕ}
    {P : Subgroup (MulAut S)} {x u : MulAut S} {V : Subgroup (MulAut S)}
    {q : TauCeti.PrimePower} (hq2 : q.p = 2) {hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) (h : KF135Hyp S p P x u V)
    (hn : p ∣ q.exponent) (h6 : p ∣ q.card ^ 6 - 1) (h1 : ¬ p ∣ q.card - 1) : False := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp7 := h.seven_le
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by omega
  have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  have hout : CFSG.RankThree.PartOne.OutStructure.OutPChain p S := by
    have hce : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hq2 (by decide) e⟩
    rw [hq2] at hce
    exact (CFSG.RankThree.PartOne.OutStructure.outPNice_trialityD4 hp hce).toChain
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e₁⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hK2 : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [hK, hq2]
  have hσ2 : ∀ c, σ c = c ^ 2 ^ q.exponent := fun c => by rw [hσ c, hq2]
  have f : S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := e.trans e₁
  obtain ⟨n₀, hn₀⟩ := hn
  have hn₀1 : 1 ≤ n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h0 | h0
    · have := q.exponent_pos
      rw [hn₀, h0, mul_zero] at this
      omega
    · exact h0
  have hqq₀ : 2 ^ q.exponent = (2 ^ n₀) ^ p := by rw [hn₀, ← pow_mul, mul_comm]
  have hq₀2 : 2 ≤ 2 ^ n₀ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n₀ := Nat.pow_le_pow_right (by norm_num) hn₀1
  have hpq₀ : ¬ p ∣ 2 ^ n₀ := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  obtain ⟨m', hm', hpm⟩ : ∃ m', (m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 6) ∧
      p ∣ CFSG.RankThree.PartOne.K128.phiNat m' (2 ^ q.exponent) := by
    rw [hcard, pow_six_sub_one_eq Nat.one_le_two_pow] at h6
    rcases (Nat.Prime.dvd_mul hp).mp h6 with h6 | h6
    · rcases (Nat.Prime.dvd_mul hp).mp h6 with h6 | h6
      · exact ⟨1, Or.inl rfl, h6⟩
      · exact ⟨2, Or.inr (Or.inl rfl), h6⟩
    · rcases (Nat.Prime.dvd_mul hp).mp h6 with h6 | h6
      · exact ⟨3, Or.inr (Or.inr (Or.inl rfl)), h6⟩
      · exact ⟨6, Or.inr (Or.inr (Or.inr rfl)), h6⟩
  have hshS := CFSG.RankThree.PartOne.K1214.SylowShape.of_mulEquiv f
    (CFSG.RankThree.PartOne.K128.sylowShape_D4 (ℓ := 2) q.exponent_pos K hK2 σ hσ2 hm' hp hp5
      hpm)
  have he2 : 2 ≤ (CFSG.RankThree.PartOne.K128.phiNat m' (2 ^ q.exponent)).factorization p := by
    rw [hqq₀] at hpm ⊢
    have h0 := CFSG.RankThree.PartOne.K128.dvd_phiNat_of_dvd_pow hp (by omega) hm' hpm
    rw [CFSG.RankThree.PartOne.K128.factorization_phiNat_pow hp hp5 hq₀2 hpq₀ hm' h0]
    have hne : CFSG.RankThree.PartOne.K128.phiNat m' (2 ^ n₀) ≠ 0 := by
      rcases hm' with rfl | rfl | rfl | rfl <;> simp only [CFSG.RankThree.PartOne.K128.phiNat] <;>
        omega
    have := (hp.dvd_iff_one_le_factorization hne).mp h0
    omega
  have h6₀ : p ∣ (2 ^ n₀) ^ 6 - 1 := by
    rw [hcard, hqq₀] at h6
    exact (CFSG.Quasithin.R3c18.dvd_pow_sub_one_iff_of_pow hp (by positivity) 6).mp h6
  have h1₀ : ¬ p ∣ 2 ^ n₀ - 1 := by
    intro h'
    apply h1
    rw [hcard, hqq₀]
    have := (CFSG.Quasithin.R3c18.dvd_pow_sub_one_iff_of_pow hp (by positivity : 0 < 2 ^ n₀)
      1).mpr (by rwa [pow_one])
    rwa [pow_one] at this
  refine false_of_E2 h hout hshS he2 f fun φ₀ hφ₀ => ?_
  obtain ⟨ψ, η, hη, hψφ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.trialityD4_stdDescent
      Nat.prime_two q.exponent_pos hK2 σ hσ2 hp hp5 φ₀ hφ₀
  have hK3 : Nat.card K = 2 ^ (3 * q.exponent) := by rw [hK2, ← pow_mul, mul_comm]
  obtain ⟨φ, hφ, hφord, hφtop, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by have := q.exponent_pos; omega : 1 ≤ 3 * q.exponent) hK3
  set δ : K ≃+* K := φ ^ (3 * n₀) with hδdef
  have hδ : ∀ c, δ c = c ^ 2 ^ (3 * n₀) := fun c => ringAut_pow_apply_of_frobenius hφ _ c
  have hδord : orderOf δ = p := by
    rw [hδdef, orderOf_pow_of_dvd (by omega) (by rw [hφord, hn₀]; exact ⟨p, by ring⟩), hφord,
      hn₀, show 3 * (p * n₀) = 3 * n₀ * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers η = Subgroup.zpowers δ := by
    have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨φ, hφtop⟩
    have h1 : Nat.card (Subgroup.zpowers η) = p := by rw [Nat.card_zpowers, hη]
    have h2 : Nat.card (Subgroup.zpowers δ) = p := by rw [Nat.card_zpowers, hδord]
    have : Finite (Subgroup.zpowers η) :=
      Nat.finite_of_card_ne_zero (by rw [h1]; exact hp.ne_zero)
    have : Finite (Subgroup.zpowers δ) :=
      Nat.finite_of_card_ne_zero (by rw [h2]; exact hp.ne_zero)
    exact IsCyclic.subgroup_eq_iff_card_eq.mpr (h1.trans h2.symm)
  have hfixeq : ∀ z, fieldActor (t := TwistTag.D4) σ η z = z ↔
      fieldActor (t := TwistTag.D4) σ δ z = z := fun z =>
    SetLike.ext_iff.1 (CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
      (fieldActorHom (t := TwistTag.D4) σ) hzp) z
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = 2 ^ (3 * n₀ * p) := by
    rw [hK3, hn₀]
    congr 1
    ring
  have hσ' : ∀ c, σ c = c ^ 2 ^ (n₀ * p) := fun c => by rw [hσ2 c, hn₀, mul_comm p n₀]
  obtain ⟨-, -, hk0, hres0, -, hJC, hfixJ, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel Nat.prime_two hn₀1
      (by omega : 2 ≤ p) hm3 K hK' σ hσ' δ hδ
  have : Finite (fixSubfield δ) := Subtype.finite
  have hβmem : ∀ y : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom),
      baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield δ).subtype y ∈
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    fun y => hJC (Subgroup.mem_map_of_mem _ y.2)
  let β : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom)
      →* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    ((baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield δ).subtype).comp
      (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom).subtype).codRestrict _ hβmem
  refine ⟨ψ, _, hψφ, ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom), inferInstance, β, fun y z hyz =>
    Subtype.ext (baseChangeGL_injective (τ := TwistTag.D4.tag) (fixSubfield δ).subtype
      (congrArg Subtype.val hyz)), fun z hz => ?_, fun y => ?_, fun A hA hAc => ?_⟩
  · have h1 : z ∈ (fieldActor (t := TwistTag.D4) σ δ).toMonoidHom.eqLocus (MonoidHom.id _) :=
      (hfixeq z).mp hz
    have h2 : (z : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ := by
      rw [← hfixJ]
      exact Subgroup.mem_map_of_mem _ h1
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp h2
    exact MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, Subtype.ext hyz⟩
  · have h2 : ((β y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ := Subgroup.mem_map_of_mem _ y.2
    rw [← hfixJ] at h2
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp h2
    have hzβ : z = β y := Subtype.ext hzy
    rw [← hzβ]
    exact (hfixeq z).mpr hz
  have hk0' : Nat.card (fixSubfield δ) = (2 ^ n₀) ^ 3 := by rw [hk0, ← pow_mul, mul_comm]
  have hfixc : ∀ c : fixSubfield δ, c ^ (2 ^ (3 * n₀)) = c := by
    intro c
    have : Fintype (fixSubfield δ) := Fintype.ofFinite _
    have h := FiniteField.pow_card c
    rwa [Fintype.card_eq_nat_card, hk0] at h
  have hpow : ∀ (t : ℕ) (c : fixSubfield δ), c ^ ((2 ^ (3 * n₀)) ^ t) = c := by
    intro t
    induction t with
    | zero => intro c; rw [pow_zero, pow_one]
    | succ t ih => intro c; rw [pow_succ, pow_mul c, ih, hfixc]
  have hσ₀ : ∀ c : fixSubfield δ, fixSubfieldRestrict σ δ c = c ^ 2 ^ (n₀ * p) := fun c =>
    Subtype.ext (by rw [hres0, hσ', SubmonoidClass.coe_pow])
  obtain ⟨t, ht⟩ : ∃ t, p = 3 * t + 1 ∨ p = 3 * t + 2 := by
    refine ⟨p / 3, ?_⟩
    have h3 : p % 3 ≠ 0 := fun h0 => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h0)
      omega
    omega
  have hsing₁ := exists_singular_D4 (k := fixSubfield δ) hn₀1 hk0'
  rcases ht with ht | ht
  ·
    refine hsing₁ (fixSubfieldRestrict σ δ) (fun c => ?_) hp hp5 h6₀ h1₀ A hA hAc
    rw [hσ₀ c, ht, show n₀ * (3 * t + 1) = 3 * n₀ * t + n₀ by ring, pow_add, pow_mul 2 (3 * n₀) t,
      pow_mul c, hpow]
  ·
    obtain ⟨φ₀, hφ₀, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two (by omega : 1 ≤ 3 * n₀) hk0
    have hσ₁ : ∀ c, (φ₀ ^ n₀) c = c ^ 2 ^ n₀ := fun c => ringAut_pow_apply_of_frobenius hφ₀ _ c
    have hσ₀2 : ∀ c, fixSubfieldRestrict σ δ c = c ^ (2 ^ n₀) ^ 2 := fun c => by
      rw [hσ₀ c, ht, show n₀ * (3 * t + 2) = 3 * n₀ * t + n₀ * 2 by ring, pow_add,
        pow_mul 2 (3 * n₀) t, pow_mul c, hpow, pow_mul]
    obtain ⟨ι⟩ := exists_mulEquiv_graphFixedRootGroup_frobenius_sq_D4 (fixSubfield δ) hk0'
      (fixSubfieldRestrict σ δ) (φ₀ ^ n₀) hσ₀2 hσ₁
    exact exists_commute_involution_of_mulEquiv ι
      (hsing₁ (φ₀ ^ n₀) hσ₁ hp hp5 h6₀ h1₀) A hA hAc

theorem false_of_kF135Hyp_D4 {S : Type} [Group S] [Finite S] {p : ℕ}
    {P : Subgroup (MulAut S)} {x u : MulAut S} {V : Subgroup (MulAut S)}
    {q : TauCeti.PrimePower} (hq2 : q.p = 2) {hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) (h : KF135Hyp S p P x u V) :
    False := by
  by_cases hres : p ∣ q.exponent ∧ p ∣ q.card ^ 6 - 1 ∧ ¬ p ∣ q.card - 1
  · exact false_of_kF135Hyp_D4_E2 hq2 e h hres.1 hres.2.1 hres.2.2
  · exact false_of_kF135Hyp_D4_of_not_E2 hq2 e h hres

theorem kF135At_fam7D4 : KF135At Fam7D4 := by
  intro S _ _ p P x u V hS h
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := hS
  exact (false_of_kF135Hyp_D4 hq2 e h).elim

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc
