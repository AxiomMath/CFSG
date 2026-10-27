module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_8_f

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section12_subgroup_of_complement_is_sigma_compl
    {M E K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E)
    (hKE : K ≤ E) :
    IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ K := by
  intro q hqK
  have hqE : q ∈ subgroupPrimeSet E :=
    hqK.trans (Subgroup.card_dvd_of_le hKE)
  exact section12_not_sigma_of_mem_complement hM hcomp hqE

public theorem CFSG.section12_fitting_sigma_compl
    {M E : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E) :
    IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ (section8FittingSubgroup E) := by
  exact section12_subgroup_of_complement_is_sigma_compl
    (G := G) (M := M) (E := E) (K := section8FittingSubgroup E)
    hM hcomp (by simpa using section8FittingSubgroup_le E)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_commutator_normal_of_normal_and_derived_le_centralizer
    {N K X : Subgroup G}
    (hKN : section10NormalIn K N) (hXN : X ≤ N)
    (hDcent : ambientDerivedSubgroup N ≤ Subgroup.centralizer (K : Set G)) :
    section10NormalIn (⁅K, X⁆) N := by
  classical
  have hN_norm_K : N ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN.1).1 hKN.2
  have hX_norm_K : X ≤ Subgroup.normalizer (K : Set G) := hXN.trans hN_norm_K
  have hKX_le_K : ⁅K, X⁆ ≤ K :=
    section12_commutator_le_left_of_le_normalizer_pre (G := G) (K := K) (A := X) hX_norm_K
  have hKX_le_N : ⁅K, X⁆ ≤ N := hKX_le_K.trans hKN.1
  have hconj {n y : G} (hn : n ∈ N) (hy : y ∈ ⁅K, X⁆) :
      n * y * n⁻¹ ∈ ⁅K, X⁆ := by
    let T : Set G := {g : G | ∃ k ∈ K, ∃ x ∈ X, ⁅k, x⁆ = g}
    have hyT : y ∈ Subgroup.closure T := by
      simpa [Subgroup.commutator_def, T] using hy
    have hgen : ∀ z, z ∈ T → n * z * n⁻¹ ∈ Subgroup.closure T := by
      intro z hz
      rcases hz with ⟨k, hkK, x, hxX, rfl⟩
      have hnK : n ∈ Subgroup.normalizer (K : Set G) := hN_norm_K hn
      have hnkK : n * k * n⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp hnK k).1 hkK
      have hxN : x ∈ N := hXN hxX
      let d : G := ⁅n, x⁆
      have hdD : d ∈ ambientDerivedSubgroup N := by
        have hdcomm : d ∈ ⁅N, N⁆ :=
          Subgroup.commutator_mem_commutator (H₁ := N) (H₂ := N) hn hxN
        simpa [d, section12_ambientDerivedSubgroup_eq_commutator] using hdcomm
      have hdC : d ∈ Subgroup.centralizer (K : Set G) := hDcent hdD
      have hnx : n * x * n⁻¹ = d * x := by
        simp [d, commutatorElement_def, mul_assoc]
      have hkd : (n * k * n⁻¹) * d = d * (n * k * n⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hdC) (n * k * n⁻¹) hnkK
      have hkxK : ⁅n * k * n⁻¹, x⁆ ∈ K :=
        hKX_le_K (Subgroup.commutator_mem_commutator (H₁ := K) (H₂ := X) hnkK hxX)
      have hcommd : ⁅n * k * n⁻¹, x⁆ * d = d * ⁅n * k * n⁻¹, x⁆ :=
        (Subgroup.mem_centralizer_iff.mp hdC) ⁅n * k * n⁻¹, x⁆ hkxK
      have heq : ⁅n * k * n⁻¹, d * x⁆ = ⁅n * k * n⁻¹, x⁆ :=
        section12_commutatorElement_mul_right_eq_of_central_pre
          (G := G) hkd hcommd
      have hconj_eq : n * ⁅k, x⁆ * n⁻¹ = ⁅n * k * n⁻¹, x⁆ := by
        calc
          n * ⁅k, x⁆ * n⁻¹ = ⁅n * k * n⁻¹, n * x * n⁻¹⁆ := by
            rw [conjugate_commutatorElement]
          _ = ⁅n * k * n⁻¹, d * x⁆ := by rw [hnx]
          _ = ⁅n * k * n⁻¹, x⁆ := heq
      rw [hconj_eq]
      exact Subgroup.subset_closure ⟨n * k * n⁻¹, hnkK, x, hxX, rfl⟩
    have hclosed : n * y * n⁻¹ ∈ Subgroup.closure T :=
      Subgroup.closure_induction (k := T)
        (p := fun z _hz => n * z * n⁻¹ ∈ Subgroup.closure T)
        (mem := hgen) (one := by simp)
        (mul := by
          intro a b _ha _hb ha hb
          simpa [mul_assoc] using (Subgroup.closure T).mul_mem ha hb)
        (inv := by
          intro a _ha ha
          simpa [mul_assoc] using (Subgroup.closure T).inv_mem ha)
        hyT
    simpa [Subgroup.commutator_def, T] using hclosed
  have hnorm :
      N ≤ Subgroup.normalizer ((⁅K, X⁆ : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconj hn
    · intro hy
      have hy' := hconj (N.inv_mem hn) hy
      simpa [mul_assoc] using hy'
  exact ⟨hKX_le_N,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX_le_N).2 hnorm⟩

/-- Corollary 12.9(a). -/
public theorem CFSG.corollary_12_9_a
    {M E E₁₂ E₁ E₂ E₃ A Q : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hq : q ∈ section12Tau1Primes M)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q E)
    (hCQ : subgroupCentralizerIn (section10Msigma M) Q = ⊥)
    (hcomm : ⁅A, Q⁆ ≠ ⊥) :
    ⁅A, Q⁆ ∈ section10PrimeOrderSubgroupsIn p A ∧
      ⁅A, Q⁆ = subgroupCentralizerIn A (section10Msigma M) ∧
        section10NormalIn ⁅A, Q⁆ M := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  haveI : Fact q.val.Prime := ⟨q.2⟩
  -- Basic facts about A
  have hAE : A ≤ E := section12_rankTwo_le hA
  rcases section12_rankTwo_elementary hA with ⟨hAcard, hAelem⟩
  haveI : IsElementaryAbelian p.val A := hAelem
  have hAcomm : IsMulCommutative A := inferInstance
  have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
  -- A is elementary abelian of order p²
  have hAcard_val : Nat.card A = p.val ^ 2 := hAcard
  -- A ⊲ E (Lemma 12.8 ensures A is normal in E)
  have hAnormE : section10NormalIn A E :=
    section12_rankTwo_normalIn_complement_of_tau2_pre hM hE hp hA
  rcases hAnormE with ⟨hAE', _hAnorm⟩
  -- Extract E-data
  rcases hE with ⟨hcomp, hE12data, hE1data, hE2data, hE3data⟩
  have hEM : E ≤ M := hcomp.2.1
  have hAM : A ≤ M := hAE.trans hEM
  -- Basic facts about Q
  rcases hQ with ⟨hQE, hQcard⟩
  have hQM : Q ≤ M := hQE.trans hEM
  -- p and q are distinct (since τ₁ and τ₂ are disjoint)
  have hp_not_sigma : p ∉ section10SigmaPrimes M := hp.1
  have hq_not_sigma : q ∉ section10SigmaPrimes M := hq.1
  have hp_ne_q : p ≠ q := by
    intro h_eq
    subst h_eq
    have hrank1 : primeRank p.val M = 1 := hq.2.2
    have hrank2 : primeRank p.val M = 2 := hp.2
    rw [hrank1] at hrank2
    omega
  have hp_prime : Nat.Prime p.val := p.2
  -- A is a σ(M)' subgroup: for every prime r, if r ∣ |A| = p², then r = p ∉ σ(M)
  have hA_sigma_compl : IsPiSubgroup (section10SigmaPrimes M)ᶜ A := by
    intro r hr_dvd
    rw [hAcard_val] at hr_dvd
    -- r.val is prime, p.val is prime, r.val ∣ p.val² → r.val = p.val
    have hr_eq_p_val : r.val = p.val :=
      Nat.prime_eq_prime_of_dvd_pow r.2 hp_prime hr_dvd
    have hr_eq_p : r = p := Subtype.ext hr_eq_p_val
    rw [hr_eq_p, Set.mem_compl_iff]
    exact hp_not_sigma
  -- A is a q'-group: for every prime r, if r ∣ |A| = p², then r ≠ q
  have hA_qprime : IsPiSubgroup (section10PPrimeSet q) A := by
    intro r hr_dvd
    rw [hAcard_val] at hr_dvd
    have hr_eq_p_val : r.val = p.val :=
      Nat.prime_eq_prime_of_dvd_pow r.2 hp_prime hr_dvd
    have hr_eq_p : r = p := Subtype.ext hr_eq_p_val
    rw [hr_eq_p]
    have hp_mem : p ∈ section10PPrimeSet q := by
      rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact hp_ne_q
    exact hp_mem
  -- Q normalizes A (since A ⊲ E and Q ≤ E)
  have hQnormA : Q ≤ Subgroup.normalizer (A : Set G) := by
    have hE_norm_A : E ≤ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAE').mp _hAnorm
    exact hQE.trans hE_norm_A
  -- [A,Q] ≤ A (commutator of a subgroup with a normalizer lies in the subgroup)
  have hAQ_le_A : ⁅A, Q⁆ ≤ A :=
    section12_commutator_le_left_of_le_normalizer_pre hQnormA
  -- Q is in the subgroup normalizer of A within M
  have hQsubnorm : Q ≤ subgroupNormalizerIn M (A : Set G) := by
    rw [subgroupNormalizerIn]
    exact le_inf hQnormA hQM
  -- Apply Proposition 10.11(d) with K = A, P = Q, p = q
  have h10_11d := proposition_10_11_d (M := M) (K := A) (P := Q) (p := q)
    hM hAM hA_sigma_compl hq_not_sigma hQsubnorm hQcard hCQ hAcomm hA_qprime
  rcases h10_11d with ⟨hAQ_cent_Msigma, hAQ_norm_M, _hAQ_cyc⟩
  -- Let C := C_A(M_σ)
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  have hAQ_le_C : ⁅A, Q⁆ ≤ C := by
    intro x hx
    refine ⟨hAQ_le_A hx, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro m hm
    exact Subgroup.mem_centralizer_iff.mp (hAQ_cent_Msigma hx) m hm
  -- Apply Proposition 10.11(b) to bound groupRank(C) ≤ 1
  have hC_groupRank : groupRank C ≤ 1 :=
    proposition_10_11_b (M := M) (K := A) hM hAM hA_sigma_compl
  -- Hence primeRank p.val C ≤ 1
  have hpC_rank : primeRank p.val C ≤ 1 := by
    calc
      primeRank p.val C ≤ groupRank C := section12_primeRank_le_groupRank (R := C) p.2
      _ ≤ 1 := hC_groupRank
  -- A has generator rank ≥ 2 (since |A| = p² and A is elementary abelian)
  have hA_genRank : 2 ≤ generatorRank A :=
    section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
      (p := p.val) hAcard
  -- generatorRank A ≤ primeRank p.val A
  -- Use the lemma with R := ↥A (the group A) and the subgroup ⊤
  have hA_primeRank : 2 ≤ primeRank p.val A := by
    let Atop : Subgroup (↥A) := ⊤
    have hAtop_p : IsPGroup p.val Atop :=
      hAp.to_subgroup Atop
    have hAtop_comm : IsMulCommutative Atop :=
      inferInstance
    have hgen_Atop : generatorRank Atop = generatorRank A := by
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      simpa [Atop] using Group.rank_congr Subgroup.topEquiv
    have hprime_ge : generatorRank Atop ≤ primeRank p.val (↥A) :=
      section12_generatorRank_le_primeRank_of_subgroup (q := p.val) hAtop_p hAtop_comm
    calc
      2 ≤ generatorRank A := hA_genRank
      _ = generatorRank Atop := hgen_Atop.symm
      _ ≤ primeRank p.val (↥A) := hprime_ge
      _ = primeRank p.val A := rfl
  -- Therefore C ≠ A, else primeRank p.val A ≤ 1 contradicts 2 ≤ primeRank p.val A
  have hCA_ne : C ≠ A := by
    intro hC_eq_A
    have h_contra : primeRank p.val A ≤ 1 :=
      hC_eq_A ▸ hpC_rank
    omega
  -- Now we prove |[A,Q]| = p
  -- Since [A,Q] ≠ ⊥, we have 1 < Nat.card [A,Q]
  haveI : Nontrivial (↥⁅A, Q⁆) := by
    refine (Subgroup.nontrivial_iff_ne_bot (H := ⁅A, Q⁆)).2 hcomm
  have hAQ_card_gt_one : 1 < Nat.card (↥⁅A, Q⁆) := by
    simpa using (Finite.one_lt_card_iff_nontrivial (α := ↥⁅A, Q⁆)).2 ‹_›
  -- [A,Q] ≤ A, so its cardinality divides |A| = p²
  have hAQ_card_dvd : Nat.card (↥⁅A, Q⁆) ∣ Nat.card A :=
    Subgroup.card_dvd_of_le hAQ_le_A
  rw [hAcard_val] at hAQ_card_dvd
  -- By Nat.dvd_prime_pow, Nat.card [A,Q] = p^k for some k ≤ 2
  have hAQ_card_eq_p : Nat.card (↥⁅A, Q⁆) = p.val := by
    rcases (Nat.dvd_prime_pow hp_prime).mp hAQ_card_dvd with ⟨k, hk, hcard_pow⟩
    -- hcard_pow : Nat.card = p.val ^ k, hk : k ≤ 2
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk_cases with (hk0 | hk1 | hk2)
    · -- k = 0: card = 1, contradicts hAQ_card_gt_one
      rw [hk0, pow_zero] at hcard_pow
      omega
    · -- k = 1: card = p.val
      rw [hk1, pow_one] at hcard_pow
      exact hcard_pow
    · -- k = 2: card = p.val ^ 2
      rw [hk2] at hcard_pow
      -- If card = p², then [A,Q] = A (same cardinality, both subgroups of A)
      -- Then C = A (since [A,Q] ≤ C ≤ A), contradiction with hCA_ne
      have hAQ_eq_A : ⁅A, Q⁆ = A := by
        apply Subgroup.eq_of_le_of_card_ge hAQ_le_A
        rw [hAcard_val, hcard_pow]
      have hC_eq_A : C = A := by
        apply le_antisymm ?_ (by simpa [hAQ_eq_A] using hAQ_le_C)
        intro x hx
        exact hx.1
      exfalso
      exact hCA_ne hC_eq_A
  -- From hAQ_card_eq_p, we get that [A,Q] is in section10PrimeOrderSubgroupsIn p A
  have hAQ_prime_order : ⁅A, Q⁆ ∈ section10PrimeOrderSubgroupsIn p A := by
    rw [section10PrimeOrderSubgroupsIn]
    refine ⟨hAQ_le_A, ?_⟩
    simpa using hAQ_card_eq_p
  -- Now we need to prove [A,Q] = C
  -- We have [A,Q] ≤ C ≤ A, and Nat.card [A,Q] = p
  -- Since C ≠ A, and C ≤ A, we must have |C| = p as well
  have hC_le_A : C ≤ A := by
    intro x hx
    exact hx.1
  have hC_card_dvd : Nat.card C ∣ Nat.card A :=
    Subgroup.card_dvd_of_le hC_le_A
  rw [hAcard_val] at hC_card_dvd
  have hC_card_eq_p : Nat.card C = p.val := by
    rcases (Nat.dvd_prime_pow hp_prime).mp hC_card_dvd with ⟨k, hk, hcard_pow⟩
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk_cases with (hk0 | hk1 | hk2)
    · -- k = 0: card = 1, but C contains [A,Q] of order p > 1
      rw [hk0, pow_zero] at hcard_pow
      have hC_nontriv : Nontrivial (↥C) := by
        refine (Subgroup.nontrivial_iff_ne_bot (H := C)).2 ?_
        intro hCbot
        apply hcomm
        exact le_bot_iff.mp (hAQ_le_C.trans (by simp [hCbot]))
      have hC_card_gt_one : 1 < Nat.card C := by
        simpa using (Finite.one_lt_card_iff_nontrivial (α := ↥C)).2 hC_nontriv
      omega
    · -- k = 1: card = p.val
      rw [hk1, pow_one] at hcard_pow
      exact hcard_pow
    · -- k = 2: card = p.val^2, then C = A (same cardinality, both subgroups of A)
      rw [hk2] at hcard_pow
      have hC_eq_A : C = A := by
        apply Subgroup.eq_of_le_of_card_ge hC_le_A
        rw [hAcard_val, hcard_pow]
      exfalso
      exact hCA_ne hC_eq_A
  -- Now [A,Q] ≤ C and both have cardinality p, so they are equal
  have hAQ_eq_C : ⁅A, Q⁆ = C := by
    apply Subgroup.eq_of_le_of_card_ge hAQ_le_C
    rw [hC_card_eq_p, hAQ_card_eq_p]
  -- Combine everything
  refine ⟨hAQ_prime_order, hAQ_eq_C, hAQ_norm_M⟩


end Section12
