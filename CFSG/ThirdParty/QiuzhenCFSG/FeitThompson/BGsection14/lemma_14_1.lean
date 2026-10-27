module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection14.Defs

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Lemma 14 1 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_msigma_le (M : Subgroup G) :
    section10Msigma M ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.2

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_ambientSylow_le
    {p : Nat.Primes} (M : Subgroup G) (S : Sylow p.val M) :
    section10AmbientSylowSubgroup M S ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.2

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_ambientSylow_isPGroup
    {p : Nat.Primes} (M : Subgroup G) (S : Sylow p.val M) :
    IsPGroup p.val (section10AmbientSylowSubgroup M S) := by
  change IsPGroup p.val ((S : Subgroup M).map M.subtype)
  exact IsPGroup.map (p := p.val) (H := (S : Subgroup M))
    S.isPGroup' M.subtype

public theorem CFSG.section14_tau_split_of_not_sigma
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpM : p ∈ subgroupPrimeSet M) (hp_not_sigma : p ∉ section10SigmaPrimes M) :
    p ∈ section12Tau2Primes M ∨ p ∈ section12Tau1Primes M ∪ section12Tau3Primes M := by
  classical
  have hpos : 1 ≤ primeRank p.val M :=
    section12_primeRank_pos_of_mem_subgroupPrimeSet (R := M) hpM
  have hle_two : primeRank p.val M ≤ 2 := by
    by_contra hnot
    have hgt : 2 < primeRank p.val M := by omega
    exact hp_not_sigma (section12_sigmaPrimes_mem_of_alphaPrimes_mem hM ⟨hpM, hgt⟩)
  have hrank : primeRank p.val M = 1 ∨ primeRank p.val M = 2 := by omega
  rcases hrank with hrank1 | hrank2
  · right
    by_cases hpD : p ∈ subgroupPrimeSet (derivedSubgroup M)
    · exact Or.inr (by simpa [section12Tau3Primes] using ⟨hp_not_sigma, hpD, hrank1⟩)
    · exact Or.inl (by simpa [section12Tau1Primes] using ⟨hp_not_sigma, hpD, hrank1⟩)
  · left
    simpa [section12Tau2Primes] using ⟨hp_not_sigma, hrank2⟩

private theorem CFSG.section14_exists_rankTwo_in_ambientSylow_of_tau2
    {M : Subgroup G} (_hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpτ2 : p ∈ section12Tau2Primes M) (S : Sylow p.val M) :
    ∃ A : Subgroup G,
      A ∈ section12RankTwoElementaryAbelianIn p M ∧
        A ≤ section10AmbientSylowSubgroup M S := by
  classical
  rcases (by simpa [section12Tau2Primes] using hpτ2) with ⟨_hpσ, hprank⟩
  have hS_rank_ge : 2 ≤ groupRank (S : Subgroup M) := by
    have hle := section10_primeRank_le_groupRank_sylow (G := M) (p := p) S
    omega
  have hS_noncyc : ¬ IsCyclic (S : Subgroup M) := by
    intro hS_cyc
    have hle : groupRank (S : Subgroup M) ≤ 1 := by
      letI : IsCyclic (S : Subgroup M) := hS_cyc
      exact groupRank_le_one_of_isCyclic (S : Subgroup M)
    omega
  let Pamb : Subgroup G := section10AmbientSylowSubgroup M S
  have hPamb_p : IsPGroup p.val Pamb := by
    simpa [Pamb] using section14_ambientSylow_isPGroup (M := M) S
  have hPamb_noncyc : ¬ IsCyclic Pamb := by
    intro hPamb_cyc
    let e : (S : Subgroup M) ≃* Pamb :=
      Subgroup.equivMapOfInjective (f := M.subtype) (S : Subgroup M) M.subtype_injective
    exact hS_noncyc (e.isCyclic.2 hPamb_cyc)
  obtain ⟨A, hA_Pamb⟩ :=
    section12_exists_rankTwo_in_noncyclic_pSubgroup
      (G := G) (P := Pamb) (p := p) hPamb_p hPamb_noncyc
  refine ⟨A, ?_, section12_rankTwo_le hA_Pamb⟩
  exact section12_rankTwo_mono hA_Pamb (by
    simpa [Pamb] using section14_ambientSylow_le (M := M) S)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
    {H R : Subgroup G} (hRnorm : R ≤ Subgroup.normalizer (H : Set G))
    (hinf : H ⊓ R = ⊥) :
    (H.subgroupOf (R ⊔ H)).IsComplement' (R.subgroupOf (R ⊔ H)) := by
  let S : Subgroup G := R ⊔ H
  let Hs : Subgroup S := H.subgroupOf S
  let Rs : Subgroup S := R.subgroupOf S
  haveI : Hs.Normal := by
    simpa [S, Hs] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := R) (N := H) hRnorm)
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxH hxR
    apply Subtype.ext
    have hxinf : ((x : S) : G) ∈ H ⊓ R := ⟨hxH, hxR⟩
    have hxbot : ((x : S) : G) ∈ (⊥ : Subgroup G) := by
      simpa [hinf] using hxinf
    simpa using hxbot
  · rw [Set.eq_univ_iff_forall]
    intro x
    have htop : Hs ⊔ Rs = ⊤ := by
      calc
        Hs ⊔ Rs = (H ⊔ R).subgroupOf S := by
          symm
          simpa [S, Hs, Rs] using
            (Subgroup.subgroupOf_sup (A := H) (A' := R) (B := S)
              le_sup_right le_sup_left)
        _ = ⊤ := by
          exact Subgroup.subgroupOf_eq_top.mpr (by simp [S, sup_comm])
    have hx_top : x ∈ Hs ⊔ Rs := by simp [htop]
    rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := Hs) (t := Rs)).1 hx_top with
      ⟨h, hhH, r, hrR, hmul⟩
    exact ⟨h, hhH, r, hrR, hmul⟩

private theorem CFSG.section14_nilpotent_msigma_of_prime_order_fixed_free
    {M R : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hRM : R ≤ M)
    (hRprime : Nat.Prime (Nat.card R))
    (hfix : subgroupCentralizerIn (section10Msigma M) R = ⊥) :
    Group.IsNilpotent (section10Msigma M) := by
  classical
  let K : Subgroup G := section10Msigma M
  let T : Subgroup G := R ⊔ K
  have hK_le_M : K ≤ M := by
    simpa [K] using section14_msigma_le M
  have hT_le_M : T ≤ M := by
    simpa [T] using sup_le hRM hK_le_M
  have hR_norm_K : R ≤ Subgroup.normalizer (K : Set G) :=
    hRM.trans (by simpa [K] using section12_le_normalizer_msigma (M := M))
  haveI : IsCyclic R := by
    haveI : Fact (Nat.Prime (Nat.card R)) := ⟨hRprime⟩
    exact isCyclic_of_prime_card (α := R) (p := Nat.card R) rfl
  have hR_le_cent : R ≤ Subgroup.centralizer (R : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact setLike_mul_comm (s := R) hx hr
  have hKRinf_bot : K ⊓ R = ⊥ := by
    apply le_bot_iff.mp
    have hle : K ⊓ R ≤ subgroupCentralizerIn K R := by
      intro x hx
      exact ⟨hx.1, hR_le_cent hx.2⟩
    simpa [K, hfix] using hle
  have hTne_top : T ≠ ⊤ := by
    intro hTtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      rw [← hTtop]
      exact hT_le_M
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hsolvT : IsSolvable T :=
    IsMinCE.proper_subgroups_solvable T (lt_top_iff_ne_top.2 hTne_top)
  have hoddT : Odd (Nat.card T) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card T)
  have hKsub_normal : (K.subgroupOf T).Normal := by
    simpa [T] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := R) (N := K) hR_norm_K)
  have hKRcomp :
      (K.subgroupOf T).IsComplement' (R.subgroupOf T) := by
    simpa [T] using
      section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
        (G := G) (H := K) (R := R) hR_norm_K hKRinf_bot
  have hRprimeT : Nat.Prime (Nat.card (R.subgroupOf T)) := by
    have hcard : Nat.card (R.subgroupOf T) = Nat.card R := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := R) (K := T) le_sup_left).toEquiv
    simpa [hcard] using hRprime
  have hfixT :
      subgroupCentralizerIn (K.subgroupOf T) (R.subgroupOf T) = ⊥ := by
    rw [subgroupCentralizerIn_subgroupOf_eq T K R le_sup_left]
    simp [K, hfix]
  have hnilKsub : Group.IsNilpotent (K.subgroupOf T) :=
    theorem_3_7 (G := T) (K.subgroupOf T) (R.subgroupOf T)
      hsolvT hoddT hKsub_normal hKRcomp hRprimeT hfixT
  let e : K.subgroupOf T ≃* K :=
    Subgroup.subgroupOfEquivOfLe (H := K) (K := T) le_sup_right
  exact (by
    simpa [K] using
      (Group.nilpotent_of_mulEquiv (G := K.subgroupOf T) (G' := K) (_h := hnilKsub) e))

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_ambientSylow_card
    {p : Nat.Primes} (M : Subgroup G) (S : Sylow p.val M) :
    Nat.card (section10AmbientSylowSubgroup M S) = Nat.card (S : Subgroup M) := by
  simpa [section10AmbientSylowSubgroup] using
    (Subgroup.card_map_of_injective
      (K := (S : Subgroup M)) (f := M.subtype) M.subtype_injective)

omit [Group G] [Finite G] [IsMinCE G] in
private theorem CFSG.section14_natCard_omegaOne_cyclic_pGroup_eq_prime
    {H : Type*} [Group H] [Finite H] {p : Nat.Primes}
    [Fact (IsPGroup p.val H)] (hcyc : IsCyclic H) [Nontrivial H] :
    Nat.card (omega₁ (G := H) (p := p.val)) = p.val := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  letI : IsCyclic H := hcyc
  letI : CommGroup H := hcyc.commGroup
  have hOmega_eq_ker : omega₁ (G := H) (p := p.val) =
      (powMonoidHom p.val : H →* H).ker := by
    apply le_antisymm
    · rw [omega₁, omega]
      refine (Subgroup.closure_le (K := (powMonoidHom p.val : H →* H).ker)).2 ?_
      intro x hx
      change x ^ (p.val ^ 1) = 1 at hx
      simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
    · intro x hx
      change x ∈ Subgroup.closure {y : H | y ^ (p.val ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
  obtain ⟨n, hn_pos, hcardH⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p.val) (G := H) (hG := Fact.out)).mp
      inferInstance
  calc
    Nat.card (omega₁ (G := H) (p := p.val))
        = Nat.card ((powMonoidHom p.val : H →* H).ker) := by rw [hOmega_eq_ker]
    _ = (Nat.card H).gcd p.val := IsCyclic.card_powMonoidHom_ker (G := H) p.val
    _ = p.val := by
      rw [hcardH]
      exact Nat.gcd_eq_right_iff_dvd.mpr
        (dvd_pow_self p.val (Nat.pos_iff_ne_zero.mp hn_pos))

omit [IsMinCE G] in
public theorem CFSG.section14_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
    {H : Subgroup G} {p : Nat.Primes}
    (hHp : IsPGroup p.val H) (hHcyc : IsCyclic H) (hHne : H ≠ ⊥) :
    Nat.card (section12OmegaOneSubgroup p H) = p.val := by
  classical
  haveI : Fact (IsPGroup p.val H) := ⟨hHp⟩
  haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hHne
  have hcard :
      Nat.card (section12OmegaOneSubgroup p H) =
        Nat.card (omega₁ (G := H) (p := p.val)) := by
    simpa [section12OmegaOneSubgroup] using
      (Subgroup.card_map_of_injective
        (K := omega₁ (G := H) (p := p.val)) (f := H.subtype) H.subtype_injective)
  exact hcard.trans
    (section14_natCard_omegaOne_cyclic_pGroup_eq_prime (H := H) (p := p) hHcyc)

private theorem CFSG.section14_omegaOne_ambientSylow_card_eq_prime_of_tau13
    {M : Subgroup G} {p : Nat.Primes}
    (hpM : p ∈ subgroupPrimeSet M)
    (hpτ13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M)
    (S : Sylow p.val M) :
    Nat.card (section12OmegaOneSubgroup p (section10AmbientSylowSubgroup M S)) =
      p.val := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  let Pamb : Subgroup G := section10AmbientSylowSubgroup M S
  have hp_dvd_M : p.val ∣ Nat.card M := by
    simpa [subgroupPrimeSet] using hpM
  have hp_dvd_G : p.val ∣ Nat.card G :=
    hp_dvd_M.trans (Subgroup.card_subgroup_dvd_card M)
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  have hrank : primeRank p.val M ≤ 1 := by
    have h := section12_tau13_primeRank_eq_one hpτ13
    omega
  have hS_cyc : IsCyclic (S : Subgroup M) :=
    section12_sylow_cyclic_of_primeRank_le_one hpodd hrank S
  have hPamb_cyc : IsCyclic Pamb := by
    let e : (S : Subgroup M) ≃* Pamb :=
      Subgroup.equivMapOfInjective (f := M.subtype) (S : Subgroup M) M.subtype_injective
    exact e.isCyclic.1 hS_cyc
  have hS_ne_bot : (S : Subgroup M) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := M) (p := p.val) S hp_dvd_M
  have hS_card_ne_one : Nat.card (S : Subgroup M) ≠ 1 := by
    intro hcard
    exact hS_ne_bot ((Subgroup.eq_bot_iff_card (H := (S : Subgroup M))).2 hcard)
  have hPamb_ne_bot : Pamb ≠ ⊥ := by
    intro hbot
    have hPamb_card : Nat.card Pamb = 1 :=
      (Subgroup.eq_bot_iff_card (H := Pamb)).1 hbot
    have hS_card : Nat.card (S : Subgroup M) = 1 := by
      exact (section14_ambientSylow_card (M := M) S).symm.trans hPamb_card
    exact hS_card_ne_one hS_card
  have hPamb_p : IsPGroup p.val Pamb := by
    simpa [Pamb] using section14_ambientSylow_isPGroup (M := M) S
  exact section14_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
    (H := Pamb) (p := p) hPamb_p hPamb_cyc hPamb_ne_bot

/-- Lemma 14.1: primes outside `σ(M) ∪ κ(M)` for `M ∉ 𝓜_{P₁}` have small
`Ω₁`, trivial fixed points on `M_σ`, and force `M_σ` nilpotent. -/
public theorem CFSG.lemma_14_1
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hMnotP1 : M ∉ section14MFamilyP1 G)
    {p : Nat.Primes}
    (hp : p ∈ subgroupPrimeSet M \ (section10SigmaPrimes M ∪ section14KappaPrimes M))
    (S : Sylow p.val M) :
    Nat.card (section12OmegaOneSubgroup p (section10AmbientSylowSubgroup M S)) ≤
        p.val ^ 2 ∧
      subgroupCentralizerIn (section10Msigma M)
          (section12OmegaOneSubgroup p (section10AmbientSylowSubgroup M S)) = ⊥ ∧
      Group.IsNilpotent (section10Msigma M) := by
  classical
  have _ : M ∉ section14MFamilyP1 G := hMnotP1
  have hpM : p ∈ subgroupPrimeSet M := hp.1
  have hp_not_union : p ∉ section10SigmaPrimes M ∪ section14KappaPrimes M := hp.2
  have hp_not_sigma : p ∉ section10SigmaPrimes M := by
    intro hpσ
    exact hp_not_union (Or.inl hpσ)
  have hp_not_kappa : p ∉ section14KappaPrimes M := by
    intro hpκ
    exact hp_not_union (Or.inr hpκ)
  rcases section14_tau_split_of_not_sigma hM hpM hp_not_sigma with hpτ2 | hpτ13
  · rcases section14_exists_rankTwo_in_ambientSylow_of_tau2 hM hpτ2 S with
      ⟨A, hA_M, hA_le_Pamb⟩
    have hΩ :
        section12OmegaOneSubgroup p (section10AmbientSylowSubgroup M S) = A :=
      ((theorem_12_5_b hM hpτ2 hA_M).2 S hA_le_Pamb).1
    have hAcard : Nat.card A = p.val ^ 2 :=
      (section12_rankTwo_elementary hA_M).1
    refine ⟨?_, ?_, ?_⟩
    · simp [hΩ, hAcard]
    · simpa [hΩ] using theorem_12_5_d hM hpτ2 hA_M
    · exact theorem_12_5_a hM hpτ2 hA_M
  · let Ω : Subgroup G :=
      section12OmegaOneSubgroup p (section10AmbientSylowSubgroup M S)
    have hΩcard : Nat.card Ω = p.val := by
      simpa [Ω] using
        section14_omegaOne_ambientSylow_card_eq_prime_of_tau13
          (G := G) (M := M) (p := p) hpM hpτ13 S
    have hΩ_le_Pamb : Ω ≤ section10AmbientSylowSubgroup M S := by
      simpa [Ω, section12OmegaOneSubgroup] using
        (Subgroup.map_subtype_le (omega₁
          (G := section10AmbientSylowSubgroup M S) (p := p.val)))
    have hΩM : Ω ≤ M :=
      hΩ_le_Pamb.trans (section14_ambientSylow_le (M := M) S)
    have hΩ_prime : Ω ∈ section10PrimeOrderSubgroupsIn p M := by
      simpa [section10PrimeOrderSubgroupsIn] using ⟨hΩM, hΩcard⟩
    have hCΩ : subgroupCentralizerIn (section10Msigma M) Ω = ⊥ := by
      by_contra hCne
      have hpκ : p ∈ section14KappaPrimes M :=
        ⟨hpτ13, ⟨Ω, hΩ_prime, hCne⟩⟩
      exact hp_not_kappa hpκ
    have hΩprime_card : Nat.Prime (Nat.card Ω) := by
      simpa [hΩcard] using p.2
    have hnil : Group.IsNilpotent (section10Msigma M) :=
      section14_nilpotent_msigma_of_prime_order_fixed_free
        hM hΩM hΩprime_card hCΩ
    refine ⟨?_, ?_, hnil⟩
    · have hp_le_sq : p.val ≤ p.val ^ 2 :=
        le_self_pow p.2.one_lt.le (by decide : 2 ≠ 0)
      simpa [Ω, hΩcard] using hp_le_sq
    · simpa [Ω] using hCΩ

end Section14
