module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection14.corollary_14_12

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Lemma 14 13 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- Lemma 14.13(a): in the nonsingleton case of Theorem 14.4, if
`σ(N)` meets `π(M)`, then `M` has type `𝓕` and no `τ₂` primes. -/
public theorem CFSG.lemma_14_13_a
    {x : G} (hx : x ≠ 1)
    (_hσ : (section14MsigmaElement x).Nonempty)
    (_hcard : 1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x})
    {M N : Subgroup G}
    (hM : M ∈ section14MsigmaElement x)
    (hN : N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hNdata : ∀ L : Subgroup G, L ∈ section14MsigmaElement x →
      section14Theorem14_4NData x (section14R x) N L)
    (hinter : ¬ Disjoint (section10SigmaPrimes N) (subgroupPrimeSet M)) :
    M ∈ section14MFamilyF G ∧
      section12Tau2Primes M = ∅ ∧
      section14FrobeniusWithKernel M (section10Msigma M) := by
  classical
  have hMx : x ∈ section10Msigma M := by simpa using hM.2
  have hxM : x ∈ M := section14_msigma_le M hMx
  have hNdataM := hNdata M hM
  rcases hNdataM with ⟨hR_eq, hRne, hcent, hSupp_tau2N, hTau2N_le_sigmaM,
      hbetaN, hcompN, hNF_or_P2⟩
  have hq_pair : (section10SigmaPrimes N ∩ subgroupPrimeSet M).Nonempty := by
    rw [Set.not_disjoint_iff_nonempty_inter] at hinter
    simpa [Set.inter_comm] using hinter
  obtain ⟨q, hqσN, hqM⟩ := hq_pair
  have hqβN : q ∈ section10BetaPrimes N := hbetaN ⟨hqM, hqσN⟩
  have hMmax : M ∈ section9MaximalSubgroups G := hM.1
  have hNmax : N ∈ section9MaximalSubgroups G := hN.1
  have hnotconjNM : section12NotConjugate N M := by
    intro a hNa
    obtain ⟨r, z, hz_zpowx, _hz_mem, _hz_ne, hzprime⟩ :=
      section14_exists_primeOrder_zpowers_in (G := G)
        (B := Subgroup.zpowers x) (Subgroup.mem_zpowers x) hx
    have hrSupp : r ∈ section14ElementPrimeSupport x := by
      have hrz : r ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
        rw [subgroupPrimeSet]
        rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
          ⟨_hzle, hrcard⟩
        simp [hrcard]
      simpa [section14ElementPrimeSupport] using
        section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hz_zpowx) hrz
    have hrTau2N : r ∈ section12Tau2Primes N := hSupp_tau2N hrSupp
    have hrTau2N_data :
        r ∉ section10SigmaPrimes N ∧ primeRank r.val N = 2 := by
      simpa [section12Tau2Primes] using hrTau2N
    have hr_not_sigmaN : r ∉ section10SigmaPrimes N := hrTau2N_data.1
    have hr_sigmaM : r ∈ section10SigmaPrimes M :=
      section14_primeSupport_subset_sigma_of_msigmaMember hM hrSupp
    have hr_sigmaN : r ∈ section10SigmaPrimes N := by
      have hr_sigmaNa : r ∈ section10SigmaPrimes (N.conjBy a) := by
        simpa [hNa] using hr_sigmaM
      have hr_sigmaN' :
          r ∈ section10SigmaPrimes ((N.conjBy a).conjBy a⁻¹) :=
        section14_sigma_mem_conjBy (L := N.conjBy a) hr_sigmaNa a⁻¹
      simpa [section11_conjBy_inv] using hr_sigmaN'
    exact hr_not_sigmaN hr_sigmaN
  have hσdis : Disjoint (section10SigmaPrimes M) (section10SigmaPrimes N) :=
    theorem_13_9 (G := G) hMmax hNmax hnotconjNM
  have hq_not_sigmaM : q ∉ section10SigmaPrimes M := by
    rw [Set.disjoint_left] at hσdis
    exact fun hqσM => hσdis hqσM hqσN
  have hqcardM : q.val ∣ Nat.card M := by
    simpa [subgroupPrimeSet] using hqM
  obtain ⟨Q, hQ⟩ :=
    section14_exists_primeOrderSubgroupIn_of_dvd_card
      (G := G) (A := M) (p := q) hqcardM
  have hQp : IsPGroup q.val Q := by
    refine IsPGroup.of_card (p := q.val) (G := Q) (n := 1) ?_
    simpa [pow_one] using hQ.2
  have hQsigmaCompl : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ Q := by
    have hQsingle : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
      section8_isPiSubgroup_singleton_of_isPGroup hQp
    intro p hpQ
    have hpq : p ∈ ({q} : Set Nat.Primes) := hQsingle p hpQ
    rw [Set.mem_compl_iff]
    rcases hpq with rfl
    exact hq_not_sigmaM
  obtain ⟨E, E₁₂, E₁, E₂, E₃, hEdata, hQleE⟩ :=
    section14_exists_EData_containing
      (G := G) (M := M) (K := Q) hMmax hQ.1 hQsigmaCompl
  have hMF : M ∈ section14MFamilyF G := by
    have hxτ2N : section14ElementPrimeSupport x ⊆ section12Tau2Primes N := hSupp_tau2N
    have hxσM : section14ElementPrimeSupport x ⊆ section10SigmaPrimes M :=
      section14_primeSupport_subset_sigma_of_msigmaMember hM
    have hσM_ne_betaM : section10SigmaPrimes M ≠ section10BetaPrimes M := by
      intro hσeqβ
      obtain ⟨r, z, hz_zpowx, _hz_mem, _hz_ne, hzprime⟩ :=
        section14_exists_primeOrder_zpowers_in (G := G)
          (B := Subgroup.zpowers x) (Subgroup.mem_zpowers x) hx
      have hrSupp : r ∈ section14ElementPrimeSupport x := by
        have hrz : r ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
          rw [subgroupPrimeSet]
          rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
            ⟨_hzle, hrcard⟩
          simp [hrcard]
        simpa [section14ElementPrimeSupport] using
          section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hz_zpowx) hrz
      have hrTau2N : r ∈ section12Tau2Primes N := hxτ2N hrSupp
      have hrσM : r ∈ section10SigmaPrimes M := hxσM hrSupp
      have hr_not_betaM : r ∉ section10BetaPrimes M := by
        obtain ⟨E₁₂, E₁, E₂, E₃, hEdata⟩ :=
          section14_exists_EData_of_complement
            (G := G) (M := N) (E := M ⊓ N) hNmax hcompN
        obtain ⟨A, hA⟩ :=
          section12_exists_rankTwo_in_E_of_tau2
            (G := G) (M := N) (E := M ⊓ N) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hNmax hEdata hrTau2N
        have hA_N : A ∈ section12RankTwoElementaryAbelianIn r N :=
          section12_rankTwo_of_EData hEdata hA
        have hr_not_betaG : r ∉ section12BetaPrimesOfGroup G :=
          (lemma_12_1_g
            (G := G) (M := N) (E := M ⊓ N) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := r)
            hNmax hEdata hrTau2N hA_N).2
        intro hrβM
        exact hr_not_betaG (by simpa [section12BetaPrimesOfGroup] using hrβM.2)
      exact hr_not_betaM (hσeqβ ▸ hrσM)
    have hM_not_P2 : M ∉ section14MFamilyP2 G := by
      intro hMP2
      have hsolvM : IsSolvable M :=
        section14_solvable_of_le_maximal (G := G) hMmax le_rfl
      obtain ⟨K, hK⟩ :=
        section14_exists_hallSubgroupIn (G := G) (H := M) hsolvM (section14KappaPrimes M)
      have hσeqβ :=
        (proposition_14_2_g (G := G) (M := M) (K := K) hMP2 hK).1
      exact hσM_ne_betaM hσeqβ
    by_cases hMP : M ∈ section14MFamilyP G
    · have hMP1 : M ∈ section14MFamilyP1 G := by
        exact section14_mem_P1_of_mem_P_and_not_mem_P2 (G := G) hMP hM_not_P2
      have hsolvM : IsSolvable M :=
        section14_solvable_of_le_maximal (G := G) hMmax le_rfl
      obtain ⟨K, hK⟩ :=
        section14_exists_hallSubgroupIn
          (G := G) (H := M) hsolvM (section14KappaPrimes M)
      have hqκM : q ∈ section14KappaPrimes M := by
        rw [hMP1.2]
        exact ⟨hqM, hq_not_sigmaM⟩
      obtain ⟨Q, hQ, hCQ⟩ :=
        section14_conjugate_kappa_witness_into_hall
          (G := G) (M := M) (K := K) hMP hK hqκM
      have hQprime : Q ∈ section12PrimeOrderSubgroups K := by
        exact ⟨hQ.1, ⟨q, hQ.2⟩⟩
      have hUniquePartner :
          section9MaximalSubgroupsContaining (Subgroup.centralizer (Q : Set G)) =
            {section14Theorem14_7Partner M K} :=
        theorem_14_7_a (G := G) (M := M) (K := K) hMP hK Q hQprime
      have hQp : IsPGroup q.val Q := by
        have hcard : Nat.card Q = q.val ^ 1 := by
          simpa [pow_one] using hQ.2
        exact IsPGroup.of_card (p := q.val) (G := Q) (n := 1) hcard
      obtain ⟨a, hQ_le_Mstar0⟩ :=
        section10_exists_conjBy_le_of_isPGroup_of_sigma
          (G := G) (M := N) (Y := Q) (p := q) hqσN hQp
      let Mstar0 : Subgroup G := N.conjBy a
      have hMstar0Max : Mstar0 ∈ section9MaximalSubgroups G := by
        simpa [Mstar0] using section14_maximal_conjBy (G := G) hNmax a
      have hqσMstar0 : q ∈ section10SigmaPrimes Mstar0 := by
        have hσeq := section14_sigmaPrimes_conjBy (G := G) N a
        simpa [Mstar0] using (hσeq.symm ▸ hqσN)
      have hqβMstar0 : q ∈ section10BetaPrimes Mstar0 := by
        exact section10_betaPrimes_of_idealPrime_of_sigma
          hMstar0Max hqβN.2 hqσMstar0
      have hQ_Mstar0 : Q ∈ section10PrimeOrderSubgroupsIn q Mstar0 := by
        exact ⟨hQ_le_Mstar0, hQ.2⟩
      have hUniqueMstar0 :
          section9MaximalSubgroupsContaining (Subgroup.centralizer (Q : Set G)) =
            {Mstar0} := by
        let Pσ : Sylow q.val (section10Msigma Mstar0) :=
          Classical.choice (Sylow.nonempty (p := q.val) (G := section10Msigma Mstar0))
        exact
          (corollary_12_14
            (G := G) (M := Mstar0) (P := Pσ) hMstar0Max hqσMstar0 hQ_Mstar0
            (Or.inl hqβMstar0)).1
      have hPartnerEq : section14Theorem14_7Partner M K = Mstar0 := by
        have hmem : Mstar0 ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (Q : Set G)) := by
          rw [hUniqueMstar0]
          simp
        have hEq : Mstar0 = section14Theorem14_7Partner M K := by
          simpa [hUniquePartner] using hmem
        exact hEq.symm
      obtain ⟨r, z, hz_zpowx, _hz_mem, _hz_ne, hzprime⟩ :=
        section14_exists_primeOrder_zpowers_in
          (G := G) (B := Subgroup.zpowers x) (Subgroup.mem_zpowers x) hx
      have hrSupp : r ∈ section14ElementPrimeSupport x := by
        have hrz : r ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
          rw [subgroupPrimeSet]
          rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
            ⟨_hzle, hrcard⟩
          simp [hrcard]
        simpa [section14ElementPrimeSupport] using
          section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hz_zpowx) hrz
      have hrTau2N : r ∈ section12Tau2Primes N := hSupp_tau2N hrSupp
      have hrTau2Mstar0 : r ∈ section12Tau2Primes Mstar0 := by
        simpa [Mstar0, section14_tau2Primes_conjBy (G := G) N a] using hrTau2N
      have hrNotKappaMstar0 : r ∉ section14KappaPrimes Mstar0 := by
        intro hrκ
        have hrτ13 : r ∈ section12Tau1Primes Mstar0 ∪ section12Tau3Primes Mstar0 :=
          section14_kappa_subset_tau13 hrκ
        rcases hrτ13 with hrτ1 | hrτ3
        · rcases (by simpa [section12Tau1Primes] using hrτ1) with
            ⟨_, _, hrank1⟩
          rcases (by simpa [section12Tau2Primes] using hrTau2Mstar0) with
            ⟨_, hrank2⟩
          omega
        · rcases (by simpa [section12Tau3Primes] using hrτ3) with
            ⟨_, _, hrank1⟩
          rcases (by simpa [section12Tau2Primes] using hrTau2Mstar0) with
            ⟨_, hrank2⟩
          omega
      have hrSigmaM : r ∈ section10SigmaPrimes M := hxσM hrSupp
      have hrPiMstar0 : r ∈ subgroupPrimeSet Mstar0 := by
        have hpos : 1 ≤ primeRank r.val Mstar0 := by
          rcases (by simpa [section12Tau2Primes] using hrTau2Mstar0) with
            ⟨_, hrank⟩
          omega
        have hdiv := section14_prime_dvd_card_of_primeRank_pos
          (R := Mstar0) (p := r) hpos
        simpa [subgroupPrimeSet] using hdiv
      have hKstarHallSigma :
          section12HallSubgroupIn (section10SigmaPrimes M) (section14KStar M K) Mstar0 := by
        simpa [hPartnerEq] using
          (theorem_14_7_b (G := G) (M := M) (K := K) hMP hK).2
      have hKstarHallKappa :
          section12HallSubgroupIn (section14KappaPrimes Mstar0) (section14KStar M K) Mstar0 := by
        simpa [hPartnerEq] using
          (theorem_14_7_b (G := G) (M := M) (K := K) hMP hK).1
      have hKstar_sub_div :
          r.val ∣ Nat.card ((section14KStar M K).subgroupOf Mstar0) := by
        have hidx_not :
            ¬ r.val ∣ ((section14KStar M K).subgroupOf Mstar0).index := by
          intro hidx
          exact (hKstarHallSigma.2.p_in_pi_of_p_dvd_index r hidx) hrSigmaM
        have hcard_mul :
            Nat.card ((section14KStar M K).subgroupOf Mstar0) *
                ((section14KStar M K).subgroupOf Mstar0).index =
              Nat.card Mstar0 := by
          simp
        have hprod : r.val ∣ Nat.card ((section14KStar M K).subgroupOf Mstar0) *
            ((section14KStar M K).subgroupOf Mstar0).index := by
          rw [hcard_mul]
          exact hrPiMstar0
        rcases r.2.dvd_mul.mp hprod with hleft | hright
        · exact hleft
        · exact False.elim (hidx_not hright)
      have hκMstar0 : r ∈ section14KappaPrimes Mstar0 := by
        exact hKstarHallKappa.2.p_in_pi_of_p_dvd_card r hKstar_sub_div
      exact False.elim (hrNotKappaMstar0 hκMstar0)
    · exact ⟨hMmax, by
        ext p
        simp
        intro hpκ
        exact hMP ⟨hMmax, ⟨p, hpκ⟩⟩⟩
  have hTau2_empty : section12Tau2Primes M = ∅ := by
    ext p
    constructor
    · intro hpτ2M
      obtain ⟨A, hA⟩ :=
        section12_exists_rankTwo_in_E_of_tau2
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hMmax hEdata hpτ2M
      have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
        section12_rankTwo_of_EData hEdata hA
      have hp_not_betaG : p ∉ section12BetaPrimesOfGroup G :=
        (lemma_12_1_g
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hMmax hEdata hpτ2M hA_M).2
      have hpM : p ∈ subgroupPrimeSet M := section12_rankTwo_prime_mem hA_M
      have hp_not_sigmaN : p ∉ section10SigmaPrimes N := by
        intro hpσN
        have hpβN : p ∈ section10BetaPrimes N := hbetaN ⟨hpM, hpσN⟩
        exact hp_not_betaG (by simpa [section12BetaPrimesOfGroup] using hpβN.2)
      have hp_not_tau2N : p ∉ section12Tau2Primes N := by
        intro hpτ2N
        exact hpτ2M.1 (hTau2N_le_sigmaM hpτ2N)
      obtain ⟨a, hQ_le_Mstar0⟩ :=
        section10_exists_conjBy_le_of_isPGroup_of_sigma
          (G := G) (M := N) (Y := Q) (p := q) hqσN hQp
      let Mstar0 : Subgroup G := N.conjBy a
      have hMstar0Max : Mstar0 ∈ section9MaximalSubgroups G := by
        simpa [Mstar0] using section14_maximal_conjBy (G := G) hNmax a
      have hqσMstar0 : q ∈ section10SigmaPrimes Mstar0 := by
        have hσeq := section14_sigmaPrimes_conjBy (G := G) N a
        simpa [Mstar0] using (hσeq.symm ▸ hqσN)
      have hqβMstar0 : q ∈ section10BetaPrimes Mstar0 := by
        exact section10_betaPrimes_of_idealPrime_of_sigma
          hMstar0Max hqβN.2 hqσMstar0
      have hQ_Mstar0 : Q ∈ section10PrimeOrderSubgroupsIn q Mstar0 := by
        exact ⟨hQ_le_Mstar0, hQ.2⟩
      have hUniqueMstar0 :
          section9MaximalSubgroupsContaining (Subgroup.centralizer (Q : Set G)) = {Mstar0} := by
        let Pσ : Sylow q.val (section10Msigma Mstar0) :=
          Classical.choice (Sylow.nonempty (p := q.val) (G := section10Msigma Mstar0))
        exact
          (corollary_12_14
            (G := G) (M := Mstar0) (P := Pσ) hMstar0Max hqσMstar0 hQ_Mstar0
            (Or.inl hqβMstar0)).1
      have hQprimeMstar0 : Q ∈ section12PrimeOrderSubgroups Mstar0 :=
        section14_primeOrderSubgroups_of_primeOrderSubgroupsIn
          (G := G) hQ_Mstar0
      have hCentQ_le_Mstar0 : Subgroup.centralizer (Q : Set G) ≤ Mstar0 := by
        exact
          (centralizer_le_normalizer Q).trans
            (section14_7_normalizer_le_of_unique_centralizer_primeOrder
              (G := G) (M := Mstar0) (A := Mstar0) (X := Q)
              hMstar0Max hQprimeMstar0 hUniqueMstar0)
      have hAQ_ne : ⁅A, Q⁆ ≠ ⊥ := by
        intro hAQbot
        have hA_le_centQ : A ≤ Subgroup.centralizer (Q : Set G) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer : ⁅A, Q⁆ = ⊥ ↔
            A ≤ Subgroup.centralizer (Q : Set G)).mp hAQbot
        have hA_le_Mstar0 : A ≤ Mstar0 := hA_le_centQ.trans hCentQ_le_Mstar0
        have hA_Mstar0 : A ∈ section12RankTwoElementaryAbelianIn p Mstar0 :=
          ⟨hA_le_Mstar0, section12_rankTwo_elementary hA⟩
        have hpMstar0 : p ∈ subgroupPrimeSet Mstar0 := section12_rankTwo_prime_mem hA_Mstar0
        have hpN : p ∈ subgroupPrimeSet N := by
          simpa [Mstar0, section14_subgroupPrimeSet_conjBy (G := G) N a] using hpMstar0
        have hpτ13N : p ∈ section12Tau1Primes N ∪ section12Tau3Primes N := by
          rcases section14_tau_split_of_not_sigma (G := G) hNmax hpN hp_not_sigmaN with
            hpτ2N | hpτ13N
          · exact False.elim (hp_not_tau2N hpτ2N)
          · exact hpτ13N
        have hprankN : primeRank p.val N = 1 :=
          section12_tau13_primeRank_eq_one hpτ13N
        have hprankMstar0 : primeRank p.val Mstar0 = 1 := by
          simpa [Mstar0, section14_primeRank_conjBy_eq (G := G) N p.val a] using hprankN
        have hprank_ge : 2 ≤ primeRank p.val Mstar0 :=
          section14_primeRank_at_least_two_of_rankTwo
            (G := G) hA_Mstar0
        omega
      have hQ_E : Q ∈ section10PrimeOrderSubgroupsIn q E := ⟨hQleE, hQ.2⟩
      have hAnorm : section10NormalIn A E :=
        (corollary_12_6_a
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hMmax hEdata hpτ2M hA).1
      have hQ_not_le_C : ¬ Q ≤ subgroupCentralizerIn E A := by
        intro hQC
        have hA_le_cent_Q : A ≤ Subgroup.centralizer (Q : Set G) := by
          intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact ((hQC hy).2 a ha).symm
        exact hAQ_ne
          ((Subgroup.commutator_eq_bot_iff_le_centralizer : ⁅A, Q⁆ = ⊥ ↔
            A ≤ Subgroup.centralizer (Q : Set G)).2 hA_le_cent_Q)
      have hqQuot :
          q ∈ section12QuotientPrimeSet (subgroupCentralizerIn E A) E :=
        section14_quotient_prime_of_primeOrder_not_le_centralizer
          (G := G) (E := E) (A := A) (Q := Q) (q := q)
          hAnorm hQ_E hQ_not_le_C
      have hqτ1M : q ∈ section12Tau1Primes M :=
        ((corollary_12_10_c
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hMmax hEdata hpτ2M hA).2.2) hqQuot
      have hCQbot : subgroupCentralizerIn (section10Msigma M) Q = ⊥ := by
        by_contra hCQne
        have hqκ : q ∈ section14KappaPrimes M :=
          ⟨Or.inl hqτ1M, ⟨Q, hQ, hCQne⟩⟩
        simp [hMF.2] at hqκ
      have h12_9a :=
        corollary_12_9_a
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
          (A := A) (Q := Q) (p := p) (q := q)
          hMmax hEdata hpτ2M hA hqτ1M hQ_E hCQbot hAQ_ne
      have h12_9b :=
        corollary_12_9_b
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
          (A := A) (Q := Q) (p := p) (q := q)
          hMmax hEdata hpτ2M hA hqτ1M hQ_E hCQbot hAQ_ne
      have h12_9c :=
        corollary_12_9_c
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
          (A := A) (Q := Q) (p := p) (q := q)
          hMmax hEdata hpτ2M hA hqτ1M hQ_E hCQbot hAQ_ne
      rcases h12_9a with ⟨hA0prime, hA0eq, _hA0normM⟩
      rcases h12_9c with ⟨hA1prime, _hA1_not_le_M⟩
      have hA0_N : ⁅A, Q⁆ ∈ section10PrimeOrderSubgroupsIn p N := by
        refine ⟨?_, hA0prime.2⟩
        intro y hy
        have hyA0 : y ∈ subgroupCentralizerIn A (section10Msigma M) := by
          simpa [hA0eq] using hy
        have hyCx : y ∈ Subgroup.centralizer ({x} : Set G) := by
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            ((Subgroup.mem_centralizer_iff.mp hyA0.2 x hMx).symm)
        exact hN.2 hyCx
      have hA1_Mstar0 : subgroupCentralizerIn A Q ∈ section10PrimeOrderSubgroupsIn p Mstar0 := by
        refine ⟨?_, hA1prime.2⟩
        intro y hy
        exact hCentQ_le_Mstar0 hy.2
      have hA1_N :
          (subgroupCentralizerIn A Q).conjBy a⁻¹ ∈ section10PrimeOrderSubgroupsIn p N := by
        have htmp :=
          section14_primeOrderSubgroupsIn_conjBy
            (G := G) (M := Mstar0) (X := subgroupCentralizerIn A Q) (p := p)
            a⁻¹ hA1_Mstar0
        simpa [Mstar0, section11_conjBy_inv] using htmp
      have hpN : p ∈ subgroupPrimeSet N := by
        simpa [subgroupPrimeSet, hA0_N.2] using (Subgroup.card_dvd_of_le hA0_N.1)
      have hprankN : primeRank p.val N = 1 :=
        section12_tau13_primeRank_eq_one (by
          rcases section14_tau_split_of_not_sigma (G := G) hNmax hpN hp_not_sigmaN with
            hpτ2N | hpτ13N
          · exact False.elim (hp_not_tau2N hpτ2N)
          · exact hpτ13N)
      obtain ⟨n, hn⟩ :=
        section14_conjBy_exists_of_primeOrderIn_primeRank_eq_one
          (G := G) (M := N) (P := ⁅A, Q⁆)
          (Q := (subgroupCentralizerIn A Q).conjBy a⁻¹) hprankN hA0_N hA1_N
      have hconj : (⁅A, Q⁆).conjBy (a * (n : G)) = subgroupCentralizerIn A Q := by
        calc
          (⁅A, Q⁆).conjBy (a * (n : G)) = ((⁅A, Q⁆).conjBy (n : G)).conjBy a := by
            symm
            exact section11_conjBy_conjBy (G := G) ⁅A, Q⁆ (n : G) a
          _ = ((subgroupCentralizerIn A Q).conjBy a⁻¹).conjBy a := by
            rw [hn]
          _ = subgroupCentralizerIn A Q := by
            simpa using section11_conjBy_inv' (G := G) (subgroupCentralizerIn A Q) a
      exact False.elim (h12_9b (a * (n : G)) hconj)
    · intro hpempty
      cases hpempty
  have hFrob : section14FrobeniusWithKernel M (section10Msigma M) := by
    let Esub : Subgroup M := E.subgroupOf M
    have hcomp : section12ComplementToMsigma M E := hEdata.1
    have hcomp' : Esub.IsComplement' (section10MsigmaSubgroup M) :=
      section14_complement_to_msigma_isComplement' (G := G) hcomp
    have hMsigma_ne : section10MsigmaSubgroup M ≠ ⊥ := by
      intro hbot
      have hxsub : (⟨x, hxM⟩ : M) ∈ section10MsigmaSubgroup M := by
        rw [← section14_msigma_subgroupOf_eq (M := M)]
        simpa [Subgroup.mem_subgroupOf] using hMx
      have hxbot : (⟨x, hxM⟩ : M) ∈ (⊥ : Subgroup M) := by
        simpa [hbot] using hxsub
      exact hx (congrArg Subtype.val (Subgroup.mem_bot.mp hxbot))
    have hEsub_ne : Esub ≠ ⊥ := by
      have hQsub_ne : Q.subgroupOf M ≠ ⊥ := by
        intro hbot
        have hcardQ : Nat.card Q = 1 := by
          calc
            Nat.card Q = Nat.card (Q.subgroupOf M) := by
              symm
              exact section12_card_subgroupOf_eq (H := Q) (K := M) hQ.1
            _ = 1 := by simp [hbot]
        exact q.2.ne_one (hQ.2.symm.trans hcardQ)
      intro hbot
      have hQsub_le : Q.subgroupOf M ≤ Esub := by
        intro y hy
        have hyQ : (y : G) ∈ Q := by
          simpa [Subgroup.mem_subgroupOf] using hy
        simpa [Esub, Subgroup.mem_subgroupOf] using hQleE hyQ
      exact hQsub_ne (le_bot_iff.mp (hQsub_le.trans (by simp [hbot])))
    refine ⟨section14_msigma_le M, Esub, ?_⟩
    have hFrobSub :
        IsFrobeniusGroupWithKernelComplement (section10MsigmaSubgroup M) Esub := by
      refine
        (lemma_3_1 (G := M) (K := section10MsigmaSubgroup M) (R := Esub)
          hMsigma_ne hEsub_ne inferInstance hcomp'.symm).2 ?_
      intro e he_ne
      by_contra hCent_ne
      obtain ⟨y, hy_ne⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp hCent_ne
      have hyCentMsub :
          ((y : elementCentralizerIn (section10MsigmaSubgroup M) (e : M)) : M) ∈
            (elementCentralizerIn (section10Msigma M) ((e : M) : G)).subgroupOf M := by
        have hyCentSub :
            ((y : elementCentralizerIn (section10MsigmaSubgroup M) (e : M)) : M) ∈
              elementCentralizerIn ((section10Msigma M).subgroupOf M) (e : M) := by
          simp [section14_msigma_subgroupOf_eq (M := M)]
        rw [section14_elementCentralizerIn_subgroupOf_eq
            (S := M) (A := section10Msigma M) (x := (e : M))] at hyCentSub
        exact hyCentSub
      have hyCent :
          (y : G) ∈ elementCentralizerIn (section10Msigma M) ((e : M) : G) := by
        simpa [Subgroup.mem_subgroupOf] using hyCentMsub
      have hyMsigma : (y : G) ∈ section10Msigma M := hyCent.1
      have hy_neG : (y : G) ≠ 1 := by
        intro hy1
        apply hy_ne
        ext
        simpa using hy1
      have he_neG : ((e : M) : G) ≠ 1 := by
        intro he1
        apply he_ne
        ext
        simpa using he1
      have he_sigma' : section14IsPiElement (section10SigmaPrimes M)ᶜ ((e : M) : G) := by
        intro p hpSupp hpσ
        have heE : ((e : M) : G) ∈ E := by
          change (e : M) ∈ E.subgroupOf M
          exact e.property
        have hpE : p ∈ subgroupPrimeSet E := by
          exact
            section8_subgroupPrimeSet_mono
              (Subgroup.zpowers_le.2 heE)
              (by simpa [section14ElementPrimeSupport] using hpSupp)
        exact section12_not_sigma_of_mem_complement (G := G) hMmax hcomp hpE hpσ
      have heCent : ((e : M) : G) ∈ elementCentralizerIn M (y : G) := by
        refine ⟨(e : M).property, ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_singleton_iff.mp hyCent.2).symm)
      have hcor :=
        corollary_14_3 (G := G) (M := M) (x := (y : G)) (x' := ((e : M) : G))
          hMmax hyMsigma hy_neG he_neG heCent he_sigma'
      obtain ⟨r, z, hzpow, _hzmem, _hzne, hzprime⟩ :=
        section14_exists_primeOrder_zpowers_in
          (G := G) (B := Subgroup.zpowers ((e : M) : G))
          (Subgroup.mem_zpowers ((e : M) : G)) he_neG
      have hrSupp : r ∈ section14ElementPrimeSupport ((e : M) : G) := by
        have hrz : r ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
          rw [subgroupPrimeSet]
          rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
            ⟨_hzle, hrcard⟩
          simp [hrcard]
        simpa [section14ElementPrimeSupport] using
          section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hzpow) hrz
      rcases hcor with hκ | hτ2
      · have hrκ : r ∈ section14KappaPrimes M := hκ.1 hrSupp
        simp [hMF.2] at hrκ
      · have hrτ2 : r ∈ section12Tau2Primes M := hτ2.1 hrSupp
        simp [hTau2_empty] at hrτ2
    simpa [section14_msigma_subgroupOf_eq (M := M)] using hFrobSub
  exact ⟨hMF, hTau2_empty, hFrob⟩

/-- Lemma 14.13(b): the chosen subgroup `N(y)` can be conjugated to `N`
by an element of `M`. -/
public theorem CFSG.lemma_14_13_b
    {x : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x})
    {M N : Subgroup G}
    (hM : M ∈ section14MsigmaElement x)
    (hN : N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hNdata : ∀ L : Subgroup G, L ∈ section14MsigmaElement x →
      section14Theorem14_4NData x (section14R x) N L)
    {y : G} (hy : y ∈ section10Msigma M) (hyne : y ≠ 1)
    (_hCy : ¬ Subgroup.centralizer ({y} : Set G) ≤ M)
    (g : G) (hgN : (section14N y).conjBy g = N) :
    ∃ m : G, m ∈ M ∧ (section14N y).conjBy m = N := by
  classical
  have hMxσ : x ∈ section10Msigma M := by
    simpa using hM.2 (by simp)
  have hxM : x ∈ M := section14_msigma_le M hMxσ
  have hxN : x ∈ N := by
    exact hN.2 (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl x))
  have hMy : M ∈ section14MsigmaElement y := by
    refine ⟨hM.1, ?_⟩
    simpa using hy
  have hσy : (section14MsigmaElement y).Nonempty := ⟨M, hMy⟩
  have hcardy :
      1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement y} :=
    section14_nonsingleton_of_conjBy_eq_maximal
      (G := G) (x := y) hyne hσy hN.1 g hgN
  have hNdataM := hNdata M hM
  rcases hNdataM with
    ⟨hR_eq, _hRne, _hcent, _hSupp_tau2N, _hTau2N_le_sigmaM,
      _hbetaN, hcompN, _hNF_or_P2⟩
  have hcompy :
      section12ComplementIn (section14N y) (section10Msigma (section14N y))
        (M ⊓ section14N y) := by
    exact theorem_14_4_e (G := G) (x := y) hyne hσy hcardy hMy
  have hcompg :
      section12ComplementIn N (section10Msigma N)
        ((M ⊓ section14N y).conjBy g) := by
    rcases hcompy with ⟨hσNy_le, hMNy_le, hsupNy, hdisjNy⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hσNy_le_conj :
          (section10Msigma (section14N y)).conjBy g ≤ (section14N y).conjBy g :=
        Subgroup.map_mono hσNy_le
      simpa [hgN, section14_msigma_conjBy (G := G) (section14N y) g] using hσNy_le_conj
    · have hMNy_le_conj :
          ((M ⊓ section14N y).conjBy g) ≤ (section14N y).conjBy g :=
        Subgroup.map_mono hMNy_le
      simpa [hgN] using hMNy_le_conj
    · calc
        N = (section14N y).conjBy g := hgN.symm
        _ = (section10Msigma (section14N y) ⊔ (M ⊓ section14N y)).conjBy g := by
              exact congrArg (fun S : Subgroup G => S.conjBy g) hsupNy
        _ = (section10Msigma (section14N y)).conjBy g ⊔
              ((M ⊓ section14N y).conjBy g) := by
              rw [Subgroup.conjBy, Subgroup.map_sup]
              rfl
        _ = section10Msigma N ⊔ ((M ⊓ section14N y).conjBy g) := by
              rw [section14_msigma_conjBy (G := G) (section14N y) g, hgN]
    · have hdisjMap :
          Disjoint ((section10Msigma (section14N y)).conjBy g)
            ((M ⊓ section14N y).conjBy g) := by
        simpa [Subgroup.conjBy] using
          (Subgroup.disjoint_map (MulAut.conj g).injective hdisjNy)
      simpa [section14_msigma_conjBy (G := G) (section14N y) g, hgN] using hdisjMap
  have hHall₁ :
      IsHallSubgroup (section10SigmaPrimes N)ᶜ
        (((M ⊓ section14N y).conjBy g).subgroupOf N) :=
    section12_msigma_complement_isHall_sigma_compl
      (G := G) (M := N) (E := (M ⊓ section14N y).conjBy g) hN.1
      (show section12ComplementToMsigma N ((M ⊓ section14N y).conjBy g) from hcompg)
  have hHall₂ :
      IsHallSubgroup (section10SigmaPrimes N)ᶜ ((M ⊓ N).subgroupOf N) :=
    section12_msigma_complement_isHall_sigma_compl
      (G := G) (M := N) (E := M ⊓ N) hN.1
      (show section12ComplementToMsigma N (M ⊓ N) from hcompN)
  have hsolvN : IsSolvable N :=
    IsMinCE.proper_subgroups_solvable N (lt_top_iff_ne_top.mpr hN.1.1)
  obtain ⟨nN, hn⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := N) hsolvN hHall₁ hHall₂
  let nG : G := nN
  have hconjInf :
      M ⊓ N = ((M ⊓ section14N y).conjBy g).conjBy nG := by
    have hmap_hn := congrArg (fun S : Subgroup N => S.map N.subtype) hn
    calc
      M ⊓ N = ((M ⊓ N).subgroupOf N).map N.subtype := by
        symm
        exact Subgroup.map_subgroupOf_eq_of_le inf_le_right
      _ = ((((M ⊓ section14N y).conjBy g).subgroupOf N).map
            (MulAut.conj nN).toMonoidHom).map N.subtype := by
          simpa using hmap_hn
      _ = ((M ⊓ section14N y).conjBy g).map
            (MulAut.conj (nN : G)).toMonoidHom := by
          change
            ((((M ⊓ section14N y).conjBy g).subgroupOf N).conjBy nN).map N.subtype =
              ((M ⊓ section14N y).conjBy g).conjBy (nN : G)
          exact section14_subgroupOf_conjBy_map_subtype hcompg.2.1 nN
      _ = ((M ⊓ section14N y).conjBy g).conjBy nG := rfl
  have hconjInf' :
      M ⊓ N = (M ⊓ section14N y).conjBy (nG * g) := by
    simpa [nG, section11_conjBy_conjBy] using hconjInf
  have hxMconj_inf : x ∈ (M ⊓ section14N y).conjBy (nG * g) := by
    simpa [hconjInf'] using (show x ∈ M ⊓ N from ⟨hxM, hxN⟩)
  have hxMconj : x ∈ M.conjBy (nG * g) :=
    (Subgroup.map_mono inf_le_left) hxMconj_inf
  have hxSigma_conj :
      section14ElementPrimeSupport x ⊆ section10SigmaPrimes (M.conjBy (nG * g)) := by
    simpa [section14_sigmaPrimes_conjBy (G := G) M (nG * g)] using
      (section14_primeSupport_subset_sigma_of_msigmaMember (G := G) hM)
  have hxMconjσ : x ∈ section10Msigma (M.conjBy (nG * g)) :=
    section14_mem_msigma_of_primeSupport_subset
      (G := G) (M := M.conjBy (nG * g))
      (section14_maximal_conjBy (G := G) hM.1 (nG * g))
      hxMconj hxSigma_conj
  have hMconj_x : M.conjBy (nG * g) ∈ section14MsigmaElement x := by
    refine ⟨section14_maximal_conjBy (G := G) hM.1 (nG * g), ?_⟩
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hxMconjσ
  have hSharp :
      section14SharpTransitiveOn (section14R x) (section14MsigmaElement x) :=
    (theorem_14_4 (G := G) (x := x) hx hσ).2.1
  obtain ⟨c, hcEq, _hcuniq⟩ :=
    hSharp (M.conjBy (nG * g)) hMconj_x M hM
  have hcNx : (c : G) ∈ elementCentralizerIn (section10Msigma N) x := by
    simpa [hR_eq] using c.property
  have hcN : (c : G) ∈ N := section14_msigma_le N hcNx.1
  have hMfix : M.conjBy ((c : G) * (nG * g)) = M := by
    calc
      M.conjBy ((c : G) * (nG * g)) = (M.conjBy (nG * g)).conjBy (c : G) := by
        symm
        exact section11_conjBy_conjBy (G := G) M (nG * g) (c : G)
      _ = M := hcEq.symm
  have hMnorm :
      Subgroup.normalizer (M : Set G) = M :=
    section14_maximal_normalizer_eq_self_of_msigma_member
      (G := G) hM.1 hMxσ hx
  have hmM : (c : G) * nG * g ∈ M := by
    have hmNorm : ((c : G) * (nG * g)) ∈ Subgroup.normalizer (M : Set G) :=
      section14_mem_normalizer_of_conjBy_eq (G := G) (H := M) hMfix
    simpa [hMnorm, mul_assoc] using hmNorm
  have hnNorm : nG ∈ Subgroup.normalizer (N : Set G) :=
    Subgroup.le_normalizer nN.property
  have hcNorm : (c : G) ∈ Subgroup.normalizer (N : Set G) :=
    Subgroup.le_normalizer hcN
  refine ⟨(c : G) * nG * g, hmM, ?_⟩
  calc
    (section14N y).conjBy ((c : G) * nG * g) =
        ((section14N y).conjBy g).conjBy ((c : G) * nG) := by
          simpa [mul_assoc] using
            (section11_conjBy_conjBy (G := G) (section14N y) g ((c : G) * nG)).symm
    _ = N.conjBy ((c : G) * nG) := by rw [hgN]
    _ = (N.conjBy nG).conjBy (c : G) := by
          simpa [mul_assoc] using
            (section11_conjBy_conjBy (G := G) N nG (c : G)).symm
    _ = N.conjBy (c : G) := by
          rw [section11_conjBy_eq_of_mem_normalizer (H := N) hnNorm]
    _ = N := section11_conjBy_eq_of_mem_normalizer (H := N) hcNorm

end Section14
