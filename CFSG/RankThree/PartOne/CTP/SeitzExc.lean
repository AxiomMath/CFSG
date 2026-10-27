module

public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.CTP.SeitzTransfer
public import CFSG.RankThree.PartOne.CTP.SeitzUToral
public import CFSG.RankThree.SteinbergR3ESmallReeAutPrimes
public import CFSG.Sporadic.Schreier.TitsOuterTwo
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.RankThree.ReeTitsAut
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem extSeitzAtInner_of_extSeitzAt {d : TauCeti.LieTypeIndex} (h : ExtSeitzAt d) :
    ExtSeitzAtInner d := fun K _ _ _ hnab hiso p hp hp5 hpd E hE hcard _ =>
  h K hnab hiso p hp hp5 hpd E hE hcard

theorem extSeitzAtOuter_of_extSeitzAt {d : TauCeti.LieTypeIndex} (h : ExtSeitzAt d) :
    ExtSeitzAtOuter d := fun K _ _ _ hnab hiso p hp hp5 hpd E hE hcard _ =>
  h K hnab hiso p hp hp5 hpd E hE hcard

theorem not_sq_dvd_tits_aut {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp5' : p ≠ 5) :
    ¬ p ^ 2 ∣ 2 * 17971200 := by
  intro h
  have hpd : p ∣ 2 * 17971200 := (dvd_pow_self p two_ne_zero).trans h
  have hN : (2 * 17971200 : ℕ) = 2 ^ 12 * 3 ^ 3 * 5 ^ 2 * 13 := by norm_num
  rw [hN] at hpd
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
        omega
    · exact hp5' ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h2))
  · have h13 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).1 h1
    subst h13
    norm_num at h

theorem extSeitzAt_tits :
    ExtSeitzAt .tits := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hcard
  by_cases hp5' : p = 5
  · exact Or.inr ⟨hp5', Or.inl rfl⟩
  exfalso
  obtain ⟨hT, -, hO, -⟩ :=
    CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound K 2 1 (reeTitsModel_tits hiso)
  have hdvd : Nat.card (MulAut K) ∣ 2 * 17971200 := by
    have := card_mulAut_dvd K
    rwa [hO, hT] at this
  have : p ^ 2 ∣ 2 * 17971200 := by
    rw [← hcard]
    exact (Subgroup.card_subgroup_dvd_card E).trans hdvd
  exact not_sq_dvd_tits_aut hp hp5 hp5' this

theorem card_mulAut_dvd_smallRee
    {T : Type} [Group T] {ℓ f : ℕ} (hf : f = 3)
    (h : ReeTitsModel T .twistedG2 ℓ f) :
    ∃ k : ℕ, Nat.card (MulAut T) ∣ 3 ^ k * ((3 ^ 3) ^ 3 * (3 ^ 3 - 1) * ((3 ^ 3) ^ 3 + 1)) := by
  obtain ⟨-, -, rfl, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier T ℓ f h
  obtain ⟨-, a', hfa', F, _, _, hF, hw⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : CharP F G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hF
  obtain ⟨E⟩ := hiso a' F hfa hF hw
  have hF' : Nat.card F = 3 ^ (2 * a' + 1) := by rw [hF, hfa]
  have ha1 : a' = 1 := by omega
  subst ha1
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element G2.tag
  obtain ⟨-, -, -, -, -, -, -, -, -, hΓ, -⟩ := small_Ree_Borel_coset_Sylow_action 1 F hF' w₀ hw₀
  obtain ⟨-, -, hFbar, ⟨R, -, -, -, -, hR3, hcompl⟩, -, -⟩ :=
    small_Ree_outer_three_kernel_field_complement 1 le_rfl F hF'
  have : Finite (G2.reeGamma F 1) := Nat.finite_of_card_ne_zero (by rw [hΓ]; norm_num)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR3
  have hout : Nat.card (Outer (G2.reeGamma F 1)) = 3 ^ (k + 1) := by
    rw [← hcompl.card_mul_card, hk, hFbar, pow_succ]
  refine ⟨k + 1, (card_mulAut_dvd T).trans (dvd_of_eq ?_)⟩
  rw [Nat.card_congr (equivalence E).toEquiv, hout, Nat.card_congr E.toEquiv, hΓ]

theorem not_sq_dvd_smallRee_aut {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ 3 ^ k * ((3 ^ 3) ^ 3 * (3 ^ 3 - 1) * ((3 ^ 3) ^ 3 + 1)) := by
  intro h
  have hp3 : ¬ p ∣ 3 ^ k := fun hd => by
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hd)
    omega
  have hcop : Nat.Coprime (p ^ 2) (3 ^ k) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hp3)
  have h2 : p ^ 2 ∣ (3 ^ 3) ^ 3 * (3 ^ 3 - 1) * ((3 ^ 3) ^ 3 + 1) := hcop.dvd_of_dvd_mul_left h
  have hpd : p ∣ (3 ^ 3) ^ 3 * (3 ^ 3 - 1) * ((3 ^ 3) ^ 3 + 1) :=
    (dvd_pow_self p two_ne_zero).trans h2
  have hN : (3 ^ 3) ^ 3 * (3 ^ 3 - 1) * ((3 ^ 3) ^ 3 + 1) = 2 ^ 3 * 3 ^ 9 * 7 * 13 * 19 * 37 := by
    norm_num
  rw [hN] at hpd h2
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h3 | h3
    · rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
      · rcases (Nat.Prime.dvd_mul hp).1 h4 with h5 | h5
        · rcases (Nat.Prime.dvd_mul hp).1 h5 with h6 | h6
          · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h6)
            omega
          · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h6)
            omega
        · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1 h5
          subst this
          norm_num at h2
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).1 h4
        subst this
        norm_num at h2
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19)).1 h3
      subst this
      norm_num at h2
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 37)).1 h1
    subst this
    norm_num at h2

theorem extSeitzAt_reeG2_one :
    ExtSeitzAt (.reeG2 1) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hcard
  exfalso
  obtain ⟨k, hk⟩ := card_mulAut_dvd_smallRee (f := 3) (ℓ := 3) rfl (reeTitsModel_reeG2 1 hiso)
  have : p ^ 2 ∣ 3 ^ k * ((3 ^ 3) ^ 3 * (3 ^ 3 - 1) * ((3 ^ 3) ^ 3 + 1)) := by
    rw [← hcard]
    exact (Subgroup.card_subgroup_dvd_card E).trans hk
  exact not_sq_dvd_smallRee_aut hp hp5 this

theorem dvd_card_outer_of_not_inner {K : Type*} [Group K] {p : ℕ} [Fact p.Prime]
    (E : Subgroup (MulAut K)) [CFSG.IsElementaryAbelian p E]
    (hout : ¬ ∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) : p ∣ Nat.card (Outer K) := by
  push Not at hout
  obtain ⟨φ, hφE, hφ⟩ := hout
  have hφp : φ ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian φ hφE
  have hψ1 : (QuotientGroup.mk φ : Outer K) ≠ 1 := fun h => by
    obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff φ).1 h
    exact hφ g hg.symm
  have hψp : (QuotientGroup.mk φ : Outer K) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hφp]
    rfl
  have := orderOf_eq_prime hψp hψ1
  rw [← this]
  exact orderOf_dvd_natCard _

theorem extSeitzAtInner_suzuki (m : ℕ) :
    ExtSeitzAtInner (.suzuki m) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hcard hinner
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hmodel := suzukiModel_of_isoLie m hiso
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hmodel
  have e' : K ≃* CFSG.Open.GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have hsyl := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
    a ha hF' e'
  have hinj := conj_injective_of_simple hnab
  obtain ⟨hE₀, hmap⟩ := inner_preimage_data (p := p) hinj E hinner
  have hcard₀ : Nat.card (E.comap (MulAut.conj : K →* MulAut K)) = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap]
    exact hcard
  have hodd : Odd (Nat.card (E.comap (MulAut.conj : K →* MulAut K))) := by
    rw [hcard₀]
    exact (hp.eq_two_or_odd'.resolve_left (by omega)).pow
  have hcyc := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.odd_commutative_subgroup_cyclic
    (E.comap (MulAut.conj : K →* MulAut K)) hodd inferInstance hsyl
  refine not_isCyclic_of_exponent_card hp ?_ hcard₀ hcyc
  intro x
  have h1 : (x : K) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (x : K) x.2
  exact Subtype.ext (by simpa using h1)

theorem extSeitzAtOuter_suzuki_of_lt_five {m : ℕ}
    (hm : 2 * m + 1 < 5) : ExtSeitzAtOuter (.suzuki m) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hcard hout
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hdvd := dvd_card_outer_of_not_inner (p := p) E hout
  have hmodel := suzukiModel_of_isoLie m hiso
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  obtain ⟨-, hout'⟩ := CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hF'
  have h1 : Nat.card (Outer K) = Nat.card (Outer (CFSG.Blueprint.suzukiGroup a F)) :=
    Nat.card_congr (equivalence e).toEquiv
  rw [h1] at hdvd
  have := Nat.le_of_dvd (by omega) (hdvd.trans hout')
  omega

end CFSG.RankThree.PartOne.CTP
