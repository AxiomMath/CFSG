module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueTypeInner
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUnique

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Quasithin (perfectCore)
open CFSG.EvenSmallLie (StandardSetting)

theorem dvd_ordA_of_dvd_pow_sub_one {m q j p : ℕ} (hm : 1 ≤ m) (hj : j ∈ Finset.Icc 2 (m + 1))
    (hp : p.Prime) (hpj : p ∣ q ^ j - 1) (hp1 : ¬ p ∣ q - 1) : p ∣ Open.ordA m q := by
  unfold Open.ordA
  have h2 : 2 ∈ Finset.Icc 2 (m + 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hq2 : q - 1 ∣ q ^ 2 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow q 1 2
    rwa [one_pow] at h
  have hdX : Nat.gcd (m + 1) (q - 1) ∣
      q ^ (m * (m + 1) / 2) * ∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i - 1) :=
    dvd_mul_of_dvd_right ((Nat.gcd_dvd_right _ _).trans
      (hq2.trans (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) h2))) _
  have hpX : p ∣ q ^ (m * (m + 1) / 2) * ∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i - 1) :=
    dvd_mul_of_dvd_right (hpj.trans (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hj)) _
  obtain ⟨c, hc⟩ := hdX
  have hd0 : 0 < Nat.gcd (m + 1) (q - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  rw [hc, Nat.mul_div_cancel_left c hd0]
  rw [hc] at hpX
  exact (hp.dvd_mul.1 hpX).resolve_left fun hpd => hp1 (hpd.trans (Nat.gcd_dvd_right _ _))

theorem not_ordA_dvd_ordTwistedA {n f : ℕ} (hn : 5 ≤ n) (hf : 1 ≤ f) :
    ¬ Open.ordA (n - 1) (2 ^ f) ∣ Open.ordTwistedA (n - 1) (2 ^ f) := by
  intro hdvd
  obtain ⟨t, ht, hnt⟩ : ∃ t, 2 ≤ t ∧ (n - 1 = 2 * t ∨ n - 1 = 2 * t + 1) := by
    rcases Nat.even_or_odd (n - 1) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨r, by omega, Or.inl (by omega)⟩
    · exact ⟨r, by omega, Or.inr hr⟩
  have hk2 : 2 ≤ f * (2 * t + 1) := by nlinarith
  have hk6 : f * (2 * t + 1) ≠ 6 := by
    intro h6
    have hj6 : 2 * t + 1 ∣ 6 := ⟨f, by rw [← h6, mul_comm]⟩
    have hj6' : 2 * t + 1 ≤ 6 := Nat.le_of_dvd (by norm_num) hj6
    have ht2 : t = 2 := by omega
    subst ht2
    norm_num at hj6
  obtain ⟨p, hp⟩ := Timmesfeld.exists_isPrimitivePrimeDivisor hk2 hk6
  have hk0 : 0 < f * (2 * t + 1) := by omega
  have hU := (Timmesfeld.Orders.profile_ordTwistedA (n := n - 1) (by omega) hf).prim p
    (f * (2 * t + 1)) hp hk0
  have hpj : p ∣ (2 ^ f) ^ (2 * t + 1) - 1 := by rw [← pow_mul]; exact hp.2.1
  have hp1 : ¬ p ∣ 2 ^ f - 1 := hp.2.2 f (by omega) (by nlinarith)
  have hpA : p ∣ Open.ordA (n - 1) (2 ^ f) :=
    dvd_ordA_of_dvd_pow_sub_one (by omega) (Finset.mem_Icc.2 ⟨by omega, by omega⟩) hp.1 hpj hp1
  exact Timmesfeld.Orders.not_zU_mid hnt (by omega) (by omega) (hU.1 (hpA.trans hdvd))

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem natCard_unitaryPSU_eq_ordTwistedA (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) :
    Nat.card (unitaryPSU h n) = Open.ordTwistedA (n - 1) (2 ^ f) :=
  LinearPilot.card_of_lieModel_PSU_two
    (lieModel_PSU_of_mulEquiv_unitaryPSU h hn hnq (MulEquiv.refl _))

section AutOrder

theorem card_mulAut_unitaryPSU_dvd (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) :
    Nat.card (MulAut (unitaryPSU h n)) ∣ Nat.card (unitaryPSU h n) * (2 ^ f + 1) * (2 * f) := by
  have := h.finite
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h' => hnq (by rw [h'.1, h'.2])
  set P := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hPdef
  have : Finite P := Finite.of_equiv _ (OutcomeLocal.primeFormOneEquiv h n).symm.toEquiv
  have hAut : Nat.card (MulAut (unitaryPSU h n)) = Nat.card (MulAut P) :=
    Nat.card_congr (MulAut.congr (OutcomeLocal.primeFormOneEquiv h n)).symm.toEquiv
  have hP : Nat.card P = Nat.card (unitaryPSU h n) :=
    Nat.card_congr (OutcomeLocal.primeFormOneEquiv h n).toEquiv
  set F := primeFormFieldFactor h (C := (1 : GL (Fin n) K)) isPrimeFormGram_one hn hq with hF
  have hker : F.ker = primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    ker_primeFormFieldFactor h isPrimeFormGram_one hn hq
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hD
  have h1 := card_ker_mul_card_range F
  rw [hker] at h1
  have h2 : Nat.card F.range ∣ 2 * f := by
    refine (Subgroup.card_subgroup_dvd_card F.range).trans (dvd_of_eq ?_)
    exact (card_ringAut_and_isCyclic Nat.prime_two K h.card).1
  set I := (inner P).subgroupOf D with hI
  have h3 : Nat.card D = Nat.card (D ⧸ I) * Nat.card I := Subgroup.card_eq_card_quotient_mul_card_subgroup I
  have h4 : Nat.card (D ⧸ I) ∣ 2 ^ f + 1 := card_primeFormD_quotient_dvd h (1 : GL (Fin n) K)
  have h5 : Nat.card I ∣ Nat.card P := by
    have hle : inner P ≤ D := inner_le_primeFormD h _
    rw [hI, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact Subgroup.card_range_dvd _
  rw [hAut, ← h1, h3, ← hP]
  calc Nat.card (D ⧸ I) * Nat.card I * Nat.card F.range ∣
        (2 ^ f + 1) * Nat.card P * (2 * f) :=
      Nat.mul_dvd_mul (Nat.mul_dvd_mul h4 h5) h2
    _ = Nat.card P * (2 ^ f + 1) * (2 * f) := by ring

theorem factorization_card_mulAut_unitaryPSU_le (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) :
    (Nat.card (MulAut (unitaryPSU h n))).factorization 2 ≤
      f * (n * (n - 1) / 2) + 1 + f.factorization 2 := by
  have := h.finite
  have hf := h.one_le
  have hdvd := card_mulAut_unitaryPSU_dvd h hn hnq
  have hU0 : Nat.card (unitaryPSU h n) ≠ 0 := Nat.card_pos.ne'
  have hq0 : 2 ^ f + 1 ≠ 0 := by positivity
  have hf0 : 2 * f ≠ 0 := by omega
  have hle := LinearPilot.factorization_two_le_of_dvd hdvd
    (mul_ne_zero (mul_ne_zero hU0 hq0) hf0)
  rw [Nat.factorization_mul (mul_ne_zero hU0 hq0) hf0, Finsupp.add_apply,
    Nat.factorization_mul hU0 hq0, Finsupp.add_apply,
    Nat.factorization_mul two_ne_zero (by omega), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two] at hle
  have hodd : (2 ^ f + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h2 =>
      (Nat.not_even_iff_odd.2 (odd_two_pow_add_one hf)) (even_iff_two_dvd.2 h2)
  obtain ⟨r, hr, hU⟩ := exists_odd_ordTwistedA_eq (m := n - 1) (by omega) hf
  have hv : (Nat.card (unitaryPSU h n)).factorization 2 = f * (n * (n - 1) / 2) := by
    rw [natCard_unitaryPSU_eq_ordTwistedA h hn hnq, hU,
      Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hr.pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.2 hr)
        (even_iff_two_dvd.2 h2)), add_zero, show n - 1 + 1 = n by omega, mul_comm (n - 1) n]
  omega

end AutOrder

section Classes

theorem card_le_card_perfectCore_fixedSubgroup_one_unitary (hn : 3 ≤ n) :
    Nat.card (unitaryPSU h n) ≤
      Nat.card (perfectCore (fixedSubgroup (1 : MulAut (projectiveSL n K)))) := by
  have := h.finite
  have htop : fixedSubgroup (1 : MulAut (projectiveSL n K)) = ⊤ :=
    eq_top_iff.2 fun y _ => rfl
  rw [htop, CFSG.Quasithin.perfectCore_eq_self_of_perfect
    (LinearPilot.commutator_projectiveSL_eq_top hn), Subgroup.card_top]
  exact Nat.card_le_card_of_injective _ (toPSL_injective h)

theorem card_perfectCore_fixedSubgroup_conj_graphFieldAut (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) (H : GL (Fin n) K) :
    Nat.card (perfectCore (fixedSubgroup
        (conjAut n K H * graphFieldAut h n * (conjAut n K H)⁻¹))) =
      Nat.card (unitaryPSU h n) := by
  have := h.finite
  rw [← LinearPilot.mulAut_congr_eq_mul, LinearPilot.card_perfectCore_fixedSubgroup_congr,
    perfectCore_fixedSubgroup_graphFieldAut h hn hnq, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (toPSL_injective h), Subgroup.card_top]

theorem card_le_card_perfectCore_fixedSubgroup_graphField (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) (A : GL (Fin n) K) {ρ : K ≃+* K} (hρ : ρ ≠ 1)
    (hθ : (conjAut n K A * fieldAut n K ρ * dualAut n K) *
      (conjAut n K A * fieldAut n K ρ * dualAut n K) = 1) :
    Nat.card (unitaryPSU h n) ≤
      Nat.card (perfectCore (fixedSubgroup (conjAut n K A * fieldAut n K ρ * dualAut n K))) := by
  have := h.finite
  obtain ⟨-, hρx, H, hH⟩ := UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two
    (by have := h.one_le; omega : 1 ≤ 2 * f) h.card hn A ρ hρ (by rw [sq]; exact hθ)
  have hρbar : ρ = barRingEquiv h := RingEquiv.ext fun x => by
    rw [hρx, barRingEquiv_apply, UnitaryFieldData.bar_apply, show 2 * f / 2 = f by omega]
  have hθ' : fieldAut n K (barRingEquiv h) * dualAut n K = graphFieldAut h n := rfl
  rw [hH, hρbar, hθ', card_perfectCore_fixedSubgroup_conj_graphFieldAut h hn hnq]

theorem not_card_perfectCore_fixedSubgroup_field_dvd (hn : 5 ≤ n) (A : GL (Fin n) K)
    {ρ : K ≃+* K} (hρ : ρ ≠ 1)
    (hθ : (conjAut n K A * fieldAut n K ρ) * (conjAut n K A * fieldAut n K ρ) = 1) :
    ¬ Nat.card (perfectCore (fixedSubgroup (conjAut n K A * fieldAut n K ρ))) ∣
      Nat.card (unitaryPSU h n) := by
  have := h.finite
  have hf := h.one_le
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hρx, H, hH⟩ := even_linear_field_involution_descent (by omega : 1 ≤ 2 * f) h.card
    (by omega) A ρ hρ (by rw [sq]; exact hθ)
  have hK₀ : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ι, σ, hσ1, hσσ, hfix⟩ := LinearPilot.exists_subfield_involution hf hK₀ h.card
  obtain ⟨-, hσx⟩ := even_and_eq_pow_of_involution (by omega : 1 ≤ 2 * f) h.card hσ1 hσσ
  have hρσ : ρ = σ := RingEquiv.ext fun x => by rw [hρx, hσx]
  rw [hH, hρσ, LinearPilot.card_perfectCore_fixedSubgroup_conj_fieldAut (by omega) ι hfix H,
    LinearPilot.natCard_projectiveSL_eq_ordA (by omega) hf hK₀,
    natCard_unitaryPSU_eq_ordTwistedA h (by omega) hnq]
  exact not_ordA_dvd_ordTwistedA hn hf

theorem not_card_centralizer_dvd_two_mul_card_mulAut_unitaryPSU (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) {y : projectiveSL n K} (hy : orderOf y = 2) :
    ¬ Nat.card (centralizer ({y} : Set (projectiveSL n K))) ∣
      2 * Nat.card (MulAut (unitaryPSU h n)) := by
  have := h.finite
  have : CharP K 2 := h.charP
  intro hdvd
  have hf := h.one_le
  have h1 := LinearPilot.le_factorization_card_centralizer_projectiveSL hf h.card hn hy
  have h2 := factorization_card_mulAut_unitaryPSU_le h hn hnq
  have h3 := LinearPilot.factorization_two_le_of_dvd hdvd
    (mul_ne_zero two_ne_zero Nat.card_pos.ne')
  rw [Nat.factorization_mul two_ne_zero Nat.card_pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two] at h3
  have hv : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  omega

end Classes

@[expose] def UnitaryGraphInvolutionExclusion (h : UnitaryFieldData 2 f K) (n : ℕ) : Prop :=
  ∀ A : GL (Fin n) K,
    (conjAut n K A * dualAut n K) * (conjAut n K A * dualAut n K) = 1 →
    Nat.card (fixedSubgroup (conjAut n K A * dualAut n K)) ∣
      2 * Nat.card (MulAut (unitaryPSU h n)) →
    ¬ Nat.card (perfectCore (fixedSubgroup (conjAut n K A * dualAut n K))) ∣
      Nat.card (unitaryPSU h n)

theorem graphFieldCoreTypeDet_of_graph (hn : 5 ≤ n) (hG : UnitaryGraphInvolutionExclusion h n) :
    GraphFieldCoreTypeDet h n := by
  have := h.finite
  have : CharP K 2 := h.charP
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  intro θ hθ h1 h2
  obtain ⟨A, ρ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (by omega : 3 ≤ n)).2 θ
  interval_cases ε
  · rw [pow_zero, mul_one] at hθ h1 h2 ⊢
    by_cases hρ : ρ = 1
    · subst hρ
      rw [map_one, mul_one] at hθ h1 h2 ⊢
      by_cases hA1 : conjAut n K A = 1
      · rw [hA1]
        exact card_le_card_perfectCore_fixedSubgroup_one_unitary h (by omega)
      · obtain ⟨y, hy, hyA⟩ :=
          OutcomeLocal.exists_involution_eq_conjAut (by omega) A (by rw [sq, hθ]) hA1
        rw [hyA, LinearPilot.fixedSubgroup_mulAut_conj_eq] at h1
        exact absurd h1 (not_card_centralizer_dvd_two_mul_card_mulAut_unitaryPSU h (by omega)
          hnq hy)
    · exact absurd h2 (not_card_perfectCore_fixedSubgroup_field_dvd h hn A hρ hθ)
  · rw [pow_one] at hθ h1 h2 ⊢
    by_cases hρ : ρ = 1
    · subst hρ
      rw [map_one, mul_one] at hθ h1 h2 ⊢
      exact absurd h2 (hG A hθ h1)
    · exact card_le_card_perfectCore_fixedSubgroup_graphField h (by omega) hnq A hρ hθ

end CFSG.SeitzReduction.UnitaryPilot
