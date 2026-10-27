module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection15.theorem_15_8
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Corollary 15 9 from BG Section 15 -/

section Section15

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
private theorem CFSG.section15_cor14_12_situation_exists_prime_mem_K
    {M H K Mstar U : Subgroup G}
    (hSituation : section15Corollary14_12Situation M H K Mstar U) :
    ∃ q : Nat.Primes, q ∈ subgroupPrimeSet K := by
  classical
  rcases hSituation with ⟨hMP2, hK, _h14, _hU, _r, _R, _hrU, _hHmax⟩
  rcases hMP2.1.2 with ⟨q, hqκ⟩
  have hqM : q ∈ subgroupPrimeSet M :=
    (section15_kappa_subset_primeSet_diff_sigma (G := G) (M := M) hqκ).1
  exact ⟨q,
    section15_subgroupPrimeSet_of_hallSubgroupIn
      (G := G) (π := section14KappaPrimes M) (K := K) (H := M)
      (p := q) hK hqκ hqM⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_E2_eq_bot_of_tau2_empty
    {M E₁₂ E₂ : Subgroup G}
    (hE₂ : section12HallSubgroupIn (section12Tau2Primes M) E₂ E₁₂)
    (hτ2empty : section12Tau2Primes M = ∅) :
    E₂ = ⊥ := by
  classical
  rcases hE₂ with ⟨hE₂E₁₂, hHallE₂⟩
  apply Subgroup.card_eq_one.mp
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro q hqprime hqdiv
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hcard_sub : Nat.card (E₂.subgroupOf E₁₂) = Nat.card E₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := E₂) (K := E₁₂) hE₂E₁₂).toEquiv
  have hqdiv_sub : q'.val ∣ Nat.card (E₂.subgroupOf E₁₂) := by
    simpa [q', hcard_sub] using hqdiv
  have hqτ2 : q' ∈ section12Tau2Primes M :=
    hHallE₂.p_in_pi_of_p_dvd_card q' hqdiv_sub
  simp [hτ2empty] at hqτ2

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_isCyclic_of_quotient_equiv_bot
    {E E₂ E₁ : Subgroup G}
    (hE₂bot : E₂ = ⊥)
    (hquot : section15QuotientMulEquiv E E₂ E₁)
    (hE₁cyc : IsCyclic E₁) :
    IsCyclic E := by
  classical
  subst E₂
  rcases hquot with ⟨_hbotE, _hbotNorm, ⟨eQ⟩⟩
  have hbot_subgroupOf :
      ((⊥ : Subgroup G).subgroupOf E) = (⊥ : Subgroup E) := by
    ext x
    simp
  let eBot : E ⧸ ((⊥ : Subgroup G).subgroupOf E) ≃* E :=
    (QuotientGroup.quotientMulEquivOfEq hbot_subgroupOf).trans
      (QuotientGroup.quotientBot (G := E))
  exact eBot.isCyclic.1 (eQ.isCyclic.2 hE₁cyc)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_corollary15_9_msigma_member
    {M : Subgroup G} {x : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hxMσ : x ∈ section10Msigma M) :
    M ∈ section14MsigmaElement x := by
  refine ⟨hM, ?_⟩
  intro z hz
  have hz_eq : z = x := by simpa using hz
  simpa [hz_eq] using hxMσ

/-- Corollary 15.9, Theorem 14.4 entry: `C_G(x) ⊄ M` gives two distinct
members `M` and `M^y` of `𝓜_σ(x)`. -/
private theorem CFSG.section15_corollary15_9_msigma_nonsingleton
    {M : Subgroup G} {x : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x} := by
  classical
  let Ωx := {L : Subgroup G // L ∈ section14MsigmaElement x}
  obtain ⟨y, hyCG, hyM⟩ := Set.not_subset.mp hCGnot
  have hMx : M ∈ section14MsigmaElement x :=
    section15_corollary15_9_msigma_member (G := G) hM hxMσ
  have hconj_x : y * x * y⁻¹ = x := by
    have hycomm : Commute y x := Subgroup.mem_centralizer_singleton_iff.mp hyCG
    calc
      y * x * y⁻¹ = x * y * y⁻¹ := by rw [hycomm.eq]
      _ = x := by simp [mul_assoc]
  have hMy : M.conjBy y ∈ section14MsigmaElement x := by
    have htmp :
        M.conjBy y ∈ section14MsigmaElement (y * x * y⁻¹) :=
      section14_msigmaElement_conjBy (G := G) (M := M) (x := x) (a := y) hMx
    simpa [hconj_x] using htmp
  have hdistinct :
      (⟨M, hMx⟩ : Ωx) ≠ ⟨M.conjBy y, hMy⟩ := by
    intro hEq
    have hMconj : M.conjBy y = M := by
      exact (congrArg Subtype.val hEq).symm
    have hyNorm : y ∈ Subgroup.normalizer (M : Set G) :=
      section15_mem_normalizer_of_conjBy_eq (G := G) (H := M) hMconj
    have hnorm_eq :
        Subgroup.normalizer (M : Set G) = M :=
      section14_maximal_normalizer_eq_self_of_msigma_member
        (G := G) hM hxMσ hxne
    exact hyM (by simpa [hnorm_eq] using hyNorm)
  have hnontriv : Nontrivial Ωx :=
    ⟨⟨M, hMx⟩, ⟨M.conjBy y, hMy⟩, hdistinct⟩
  simpa [Ωx] using
    (Finite.one_lt_card_iff_nontrivial (α := Ωx)).2 hnontriv

private theorem CFSG.section15_corollary15_9_theorem14_4_data
    {M N : Subgroup G} {x : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (hN : N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    ∀ L : Subgroup G, L ∈ section14MsigmaElement x →
      section14Theorem14_4NData x (section14R x) N L := by
  classical
  have hMx : M ∈ section14MsigmaElement x :=
    section15_corollary15_9_msigma_member (G := G) hM hxMσ
  have hσ : (section14MsigmaElement x).Nonempty := ⟨M, hMx⟩
  have hcard :
      1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x} :=
    section15_corollary15_9_msigma_nonsingleton
      (G := G) hM hxMσ hxne hCGnot
  rcases (theorem_14_4 (G := G) (x := x) hxne hσ).2.2 hcard with
    ⟨N0, _hN0, hN0data, hN0uniq⟩
  have hN_eq : N = N0 := hN0uniq N hN
  intro L hL
  simpa [hN_eq] using hN0data L hL

private theorem CFSG.section15_corollary15_9_initial_data
    {M N : Subgroup G} {x : G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (hN : N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNnotF : N ∉ section14MFamilyF G)
    (hr : r ∈ subgroupPrimeSet (Subgroup.zpowers x)) :
    N ∈ section14MFamilyP2 G ∧
      r ∈ section12Tau2Primes N ∧
        r ∈ section10SigmaPrimes M ∧
          section12ComplementIn N (section10Msigma N) (M ⊓ N) := by
  classical
  have hMx : M ∈ section14MsigmaElement x :=
    section15_corollary15_9_msigma_member (G := G) hM hxMσ
  have hNdataM :=
    section15_corollary15_9_theorem14_4_data
      (G := G) hM hxMσ hxne hN hCGnot M hMx
  rcases hNdataM with
    ⟨_hR_eq, _hRne, _hcent, hSupp_tau2N, hTau2N_le_sigmaM,
      _hbetaN, hcompN, hNF_or_P2⟩
  have hrTau : r ∈ section12Tau2Primes N := by
    exact hSupp_tau2N (by simpa [section14ElementPrimeSupport] using hr)
  have hNP2 : N ∈ section14MFamilyP2 G := by
    rcases hNF_or_P2 with hNF | hNP2
    · exact False.elim (hNnotF hNF)
    · exact hNP2
  exact ⟨hNP2, hrTau, hTau2N_le_sigmaM hrTau, hcompN⟩

omit [Finite G] [IsMinCE G] in
/-- Corollary 15.9 source bridge: the Sylow `r`-subgroup of the
Proposition 14.2(a) complement `U` has normalizer contained in the original
maximal subgroup `M`. -/
private theorem CFSG.section15_ambientSylow_le
    {M : Subgroup G} {p : Nat.Primes} (S : Sylow p.val M) :
    section10AmbientSylowSubgroup M S ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.2

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_ambientSylow_isPGroup
    {M : Subgroup G} {p : Nat.Primes} (S : Sylow p.val M) :
    IsPGroup p.val (section10AmbientSylowSubgroup M S) := by
  change IsPGroup p.val ((S : Subgroup M).map M.subtype)
  exact IsPGroup.map (p := p.val) (H := (S : Subgroup M)) S.isPGroup' M.subtype

private theorem CFSG.section15_exists_rankTwo_in_ambientSylow_of_tau2
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
    simpa [Pamb] using section15_ambientSylow_isPGroup (M := M) S
  have hPamb_noncyc : ¬ IsCyclic Pamb := by
    intro hPamb_cyc
    let e : (S : Subgroup M) ≃* Pamb :=
      Subgroup.equivMapOfInjective (f := M.subtype) (S : Subgroup M) M.subtype_injective
    exact hS_noncyc (e.isCyclic.2 hPamb_cyc)
  obtain ⟨A, hA_Pamb⟩ :=
    section15_exists_rankTwo_in_noncyclic_pSubgroup
      (G := G) (P := Pamb) (p := p) hPamb_p hPamb_noncyc
  refine ⟨A, ?_, section12_rankTwo_le hA_Pamb⟩
  exact section12_rankTwo_mono hA_Pamb (by
    simpa [Pamb] using section15_ambientSylow_le (M := M) S)

omit [IsMinCE G] in
private theorem CFSG.section15_ambientSylow_isSylow_of_hall
    {H K : Subgroup G} {π : Set Nat.Primes} {q : Nat.Primes}
    (hHall : section12HallSubgroupIn π K H) (hqπ : q ∈ π)
    (Q : Sylow q.val K) :
    ∃ S : Sylow q.val H,
      section10AmbientSylowSubgroup H S = section10AmbientSylowSubgroup K Q := by
  classical
  rcases hHall with ⟨hKH, hHallK⟩
  haveI : Fact q.val.Prime := ⟨q.2⟩
  have hQamb_le_H : section10AmbientSylowSubgroup K Q ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact hKH y.2
  let R : Subgroup H := (section10AmbientSylowSubgroup K Q).subgroupOf H
  have hR_p : IsPGroup q.val R := by
    have hRG : IsPGroup q.val (section10AmbientSylowSubgroup K Q) :=
      section15_ambientSylow_isPGroup (M := K) Q
    exact hRG.of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (H := section10AmbientSylowSubgroup K Q) (K := H) hQamb_le_H).symm
  have hR_map : R.map H.subtype = section10AmbientSylowSubgroup K Q := by
    simp [R, inf_eq_left.2 hQamb_le_H]
  have hR_not_dvd : ¬ q.val ∣ R.index := by
    intro hidx
    have hR_card : Nat.card R = Nat.card (Q : Subgroup K) := by
      calc
        Nat.card R = Nat.card (section10AmbientSylowSubgroup K Q) := by
          simpa [R] using section12_card_subgroupOf_eq hQamb_le_H
        _ = Nat.card (Q : Subgroup K) := by
          simpa [section10AmbientSylowSubgroup] using
            (Subgroup.card_map_of_injective
              (K := (Q : Subgroup K)) (f := K.subtype) K.subtype_injective)
    have hK_card : Nat.card (K.subgroupOf H) = Nat.card K :=
      section12_card_subgroupOf_eq hKH
    have hidx2 :
        R.index = (Q : Subgroup K).index * (K.subgroupOf H).index := by
      have hmul :
          Nat.card R * R.index =
            Nat.card (Q : Subgroup K) * ((Q : Subgroup K).index * (K.subgroupOf H).index) := by
        calc
          Nat.card R * R.index = Nat.card H := R.card_mul_index
          _ = Nat.card (K.subgroupOf H) * (K.subgroupOf H).index := by
            rw [Subgroup.card_mul_index]
          _ = Nat.card K * (K.subgroupOf H).index := by rw [hK_card]
          _ = (Nat.card (Q : Subgroup K) * (Q : Subgroup K).index) *
                (K.subgroupOf H).index := by rw [Subgroup.card_mul_index]
          _ = Nat.card (Q : Subgroup K) * ((Q : Subgroup K).index *
                (K.subgroupOf H).index) := by ring
      rw [hR_card] at hmul
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul
    have hq_dvd_mul : q.val ∣ (Q : Subgroup K).index * (K.subgroupOf H).index := by
      simpa [hidx2] using hidx
    rcases q.2.dvd_mul.mp hq_dvd_mul with hqQ | hqK
    · exact Q.not_dvd_index hqQ
    · exact (hHallK.p_in_pi_of_p_dvd_index q hqK) hqπ
  let S : Sylow q.val H := IsPGroup.toSylow (p := q.val) hR_p hR_not_dvd
  refine ⟨S, ?_⟩
  calc
    section10AmbientSylowSubgroup H S = R.map H.subtype := by
      simp [S, section10AmbientSylowSubgroup]
    _ = section10AmbientSylowSubgroup K Q := hR_map

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_corollary15_9_ambientSylow_U_le_M
    {M N K U : Subgroup G} {r : Nat.Primes}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hN : N ∈ section9MaximalSubgroups G)
    (_hcomp : section12ComplementIn N (section10Msigma N) (M ⊓ N))
    (_hKleMN : K ≤ M ⊓ N)
    (hUleMN : U ≤ M ⊓ N)
    (_hrτ2 : r ∈ section12Tau2Primes N)
    (_hrσM : r ∈ section10SigmaPrimes M)
    (_hU : section14Proposition14_2AData N K U)
    (R : Sylow r.val U) :
    section10AmbientSylowSubgroup U R ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hyR, rfl⟩
  exact (hUleMN y.2).1

private theorem CFSG.section15_corollary15_9_ambientSylow_U_noncyclic
    {M N K U : Subgroup G} {r : Nat.Primes}
    (hN : N ∈ section9MaximalSubgroups G)
    (_hcomp : section12ComplementIn N (section10Msigma N) (M ⊓ N))
    (hrτ2 : r ∈ section12Tau2Primes N)
    (hU : section14Proposition14_2AData N K U)
    (R : Sylow r.val U) :
    ¬ IsCyclic (section10AmbientSylowSubgroup U R) := by
  classical
  rcases hU with ⟨_hprime, _hcomm, hUHall, _hreg, _hnormComp⟩
  have hrπ :
      r ∈ ((section14KappaPrimes N ∪ section10SigmaPrimes N)ᶜ) := by
    intro hrκσ
    rcases hrκσ with hrκ | hrσ
    · exact section15_tau2_not_mem_kappa (G := G) (M := N) hrτ2 hrκ
    · exact hrτ2.1 hrσ
  rcases section15_ambientSylow_isSylow_of_hall
      (G := G) (H := N) (K := U)
      (π := ((section14KappaPrimes N ∪ section10SigmaPrimes N)ᶜ))
      (q := r) hUHall hrπ R with
    ⟨S, hS⟩
  rcases section15_exists_rankTwo_in_ambientSylow_of_tau2
      (G := G) (M := N) (p := r) hN hrτ2 S with
    ⟨A, hA, hAleS⟩
  intro hcyc
  have hAleR : A ≤ section10AmbientSylowSubgroup U R := by
    simpa [hS] using hAleS
  rcases section12_rankTwo_elementary hA with ⟨hAcard, hAelem⟩
  have hRank :
      2 ≤ groupRank (section10AmbientSylowSubgroup U R) :=
    section15_groupRank_at_least_two_of_rankTwo_elementary_le
      (G := G) (K := section10AmbientSylowSubgroup U R) (A := A) (p := r)
      hAleR ⟨hAcard, hAelem⟩
  have hRank_le : groupRank (section10AmbientSylowSubgroup U R) ≤ 1 := by
    letI : IsCyclic (section10AmbientSylowSubgroup U R) := hcyc
    exact groupRank_le_one_of_isCyclic (section10AmbientSylowSubgroup U R)
  omega

private theorem CFSG.section15_corollary15_9_normalizer_ambientSylow_U_le_M
    {M N K U : Subgroup G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hN : N ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementIn N (section10Msigma N) (M ⊓ N))
    (hKleMN : K ≤ M ⊓ N)
    (hUleMN : U ≤ M ⊓ N)
    (hrτ2 : r ∈ section12Tau2Primes N)
    (hrσM : r ∈ section10SigmaPrimes M)
    (hU : section14Proposition14_2AData N K U)
    (R : Sylow r.val U) :
    Subgroup.normalizer (section10AmbientSylowSubgroup U R : Set G) ≤ M := by
  classical
  have hPp : IsPGroup r.val (section10AmbientSylowSubgroup U R) := by
    change IsPGroup r.val ((R : Subgroup U).map U.subtype)
    exact IsPGroup.map (p := r.val) (H := (R : Subgroup U)) R.isPGroup' U.subtype
  exact corollary_12_10_d
    (G := G) (M := M) (P := section10AmbientSylowSubgroup U R) (p := r)
    hM hrσM hPp
    (section15_corollary15_9_ambientSylow_U_le_M
      (G := G) (M := M) (N := N) (K := K) (U := U) (r := r)
      hM hN hcomp hKleMN hUleMN hrτ2 hrσM hU R)
    (section15_corollary15_9_ambientSylow_U_noncyclic
      (G := G) (M := M) (N := N) (K := K) (U := U) (r := r)
      hN hcomp hrτ2 hU R)

private theorem CFSG.section15_corollary15_9_cor14_12_situation
    {M N K U Mstar : Subgroup G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hInitial :
      N ∈ section14MFamilyP2 G ∧
        r ∈ section12Tau2Primes N ∧
          r ∈ section10SigmaPrimes M ∧
            section12ComplementIn N (section10Msigma N) (M ⊓ N))
    (hK : section12HallSubgroupIn (section14KappaPrimes N) K N)
    (hKleMN : K ≤ M ⊓ N)
    (hUleMN : U ≤ M ⊓ N)
    (hU : section14Proposition14_2AData N K U)
    (h14 : section14Theorem14_7Data N K Mstar) :
    section15Corollary14_12Situation N M K Mstar U := by
  classical
  rcases hInitial with ⟨hNP2, hrτ2, hrσM, hcompN⟩
  let R : Sylow r.val U := Classical.choice (Sylow.nonempty (p := r.val) (G := U))
  have hrU : r ∈ subgroupPrimeSet U :=
    section15_tau2_mem_prop14_U_primeSet_of_complement
      (G := G) (M := M) (N := N) (K := K) (U := U) (r := r)
      hNP2.1.1 hcompN hrτ2 hU
  have hNorm_le_M :
      Subgroup.normalizer (section10AmbientSylowSubgroup U R : Set G) ≤ M :=
    section15_corollary15_9_normalizer_ambientSylow_U_le_M
      (G := G) (M := M) (N := N) (K := K) (U := U) (r := r)
      hM hNP2.1.1 hcompN hKleMN hUleMN hrτ2 hrσM hU R
  exact ⟨hNP2, hK, h14, hU, r, R, hrU, ⟨hM, hNorm_le_M⟩⟩

private theorem CFSG.section15_msigma_nilpotent_of_mem_MFamilyF
    {M : Subgroup G}
    (hMFam : M ∈ section14MFamilyF G) :
    Group.IsNilpotent (section10Msigma M) := by
  classical
  by_contra hnotNil
  have hP1 : M ∈ section14MFamilyP1 G :=
    section15_lemma_14_1_nonnilpotent_msigma_mem_familyP1
      (G := G) (M := M) hMFam.1 hnotNil
  rcases (by
      simpa [section14MFamilyP1, section14MFamilyP] using hP1) with
    ⟨⟨_hmax, hκnonempty⟩, _hκeq⟩
  rcases hκnonempty with ⟨p, hpκ⟩
  have hpempty : p ∈ (∅ : Set Nat.Primes) := by
    simp [hMFam.2] at hpκ
  exact hpempty

private theorem CFSG.section15_msigma_le_fitting_of_mem_MFamilyF
    {M : Subgroup G}
    (hMFam : M ∈ section14MFamilyF G) :
    section10Msigma M ≤ section8FittingSubgroup M := by
  exact
    section15_MF_le_fitting
      (M := M) (MF := section10Msigma M)
      (section15_msigma_MFSubgroup_of_nilpotent
        (G := G) (M := M) hMFam.1
        (section15_msigma_nilpotent_of_mem_MFamilyF
          (G := G) (M := M) hMFam))

private theorem CFSG.section15_fitting_not_ti_of_mem_fitting_and_external_centralizer
    {M : Subgroup G} {x : G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hxF : x ∈ section8FittingSubgroup M)
    (hxne : x ≠ 1)
    (hr : r ∈ subgroupPrimeSet (Subgroup.zpowers x))
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    ¬ section14TISubgroup (section8FittingSubgroup M) := by
  classical
  have hzpow_le_F : Subgroup.zpowers x ≤ section8FittingSubgroup M :=
    Subgroup.zpowers_le.2 hxF
  have hrF : r ∈ subgroupPrimeSet (section8FittingSubgroup M) :=
    section8_subgroupPrimeSet_mono hzpow_le_F hr
  have hM8 : M ∈ section8MaximalSubgroups G := by
    simpa [section8MaximalSubgroups, section9MaximalSubgroups] using hM
  have hNormF :
      Subgroup.normalizer (section8FittingSubgroup M : Set G) = M :=
    section8_normalizer_fittingSubgroup_eq (G := G) (M := M) (q := r) hM8 hrF
  obtain ⟨g, hgC, hgM⟩ := Set.not_subset.mp hCGnot
  have hgNorm_not : g ∉ Subgroup.normalizer (section8FittingSubgroup M : Set G) := by
    intro hgNorm
    exact hgM (by simpa [hNormF] using hgNorm)
  have hgcomm : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hx_conj_eq : g⁻¹ * x * g = x := by
    calc
      g⁻¹ * x * g = g⁻¹ * (x * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * x) := by rw [← hgcomm.eq]
      _ = x := by simp
  have hxConj :
      x ∈ section14SetConjBy (section8FittingSubgroup M : Set G) g := by
    exact ⟨x, hxF, hx_conj_eq.symm⟩
  intro hTI
  have hx_one_mem : x ∈ ({1} : Set G) :=
    hTI.2.2.2 g hgNorm_not ⟨hxF, hxConj⟩
  exact hxne (by simpa using hx_one_mem)

private theorem CFSG.section15_fitting_not_ti_of_MFamilyF_msigma_element
    {M : Subgroup G} {x : G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMFam : M ∈ section14MFamilyF G)
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (hr : r ∈ subgroupPrimeSet (Subgroup.zpowers x))
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    ¬ section14TISubgroup (section8FittingSubgroup M) := by
  exact
    section15_fitting_not_ti_of_mem_fitting_and_external_centralizer
      (G := G) (M := M) (x := x) (r := r) hM
      (section15_msigma_le_fitting_of_mem_MFamilyF
        (G := G) (M := M) hMFam hxMσ)
      hxne hr hCGnot

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_fitting_intersection_ne_bot_of_mem_fitting_and_external_centralizer
    {M : Subgroup G} {x : G}
    (hxF : x ∈ section8FittingSubgroup M)
    (hxne : x ≠ 1)
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    ∃ g : G,
      g ∉ M ∧
        section8FittingSubgroup M ⊓
            (section8FittingSubgroup M).conjBy g ≠ ⊥ := by
  classical
  obtain ⟨g, hgC, hgM⟩ := Set.not_subset.mp hCGnot
  refine ⟨g, hgM, ?_⟩
  intro hbot
  have hgcomm : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hx_conj_eq : g * x * g⁻¹ = x := by
    calc
      g * x * g⁻¹ = x * g * g⁻¹ := by rw [hgcomm.eq]
      _ = x := by simp [mul_assoc]
  have hxConj : x ∈ (section8FittingSubgroup M).conjBy g := by
    exact Subgroup.mem_map.mpr ⟨x, hxF, by
      simpa [Subgroup.conjBy, MulAut.conj_apply] using hx_conj_eq⟩
  have hxInf :
      x ∈ section8FittingSubgroup M ⊓
          (section8FittingSubgroup M).conjBy g := ⟨hxF, hxConj⟩
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    simpa [hbot] using hxInf
  exact hxne (by simpa using hxbot)

private theorem CFSG.section15_complement_cyclic_of_tau2_empty
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G} {x : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMFam : M ∈ section14MFamilyF G)
    (hMFsub : section15MFSubgroup M (section10Msigma M))
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (hEdata : section12EData M E E₁₂ E₁ E₂ E₃)
    (hτ2empty : section12Tau2Primes M = ∅) :
    IsCyclic E := by
  classical
  rcases
      section15_fitting_intersection_ne_bot_of_mem_fitting_and_external_centralizer
        (G := G) (M := M) (x := x)
        (section15_msigma_le_fitting_of_mem_MFamilyF
          (G := G) (M := M) hMFam hxMσ)
        hxne hCGnot with
    ⟨g, hgM, hXne⟩
  let X : Subgroup G :=
    section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g
  have h15d :
      E₃ = ⊥ ∧ section10NormalIn E₂ E ∧
        section15QuotientMulEquiv E E₂ E₁ ∧ IsCyclic E₁ := by
    exact
      theorem_15_7_d
        (G := G) (M := M) (MF := section10Msigma M) (X := X)
        (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
        (g := g) hM hMFsub hnotTI hgM rfl (by simpa [X] using hXne) hEdata
  have hE2bot : E₂ = ⊥ :=
    section15_E2_eq_bot_of_tau2_empty (G := G) hEdata.2.2.2.1 hτ2empty
  exact section15_isCyclic_of_quotient_equiv_bot
    (G := G) hE2bot h15d.2.2.1 h15d.2.2.2

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_ne_bot_of_prime_mem_le_fitting
    {E K : Subgroup G} {q : Nat.Primes}
    (hKleF : K ≤ section8FittingSubgroup E)
    (hqK : q ∈ subgroupPrimeSet K) :
    E ≠ ⊥ := by
  intro hEbot
  have hKleE : K ≤ E := hKleF.trans (section8FittingSubgroup_le E)
  have hKbot : K = ⊥ := by
    exact le_bot_iff.mp (by simpa [hEbot] using hKleE)
  have hq_dvd_one : q.val ∣ 1 := by
    simpa [subgroupPrimeSet, hKbot] using hqK
  exact q.property.not_dvd_one hq_dvd_one

private theorem CFSG.section15_frobenius_msigma_of_tau2_empty
    {M E : Subgroup G} {x : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMFam : M ∈ section14MFamilyF G)
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (hcomp : section12ComplementToMsigma M E)
    (hEne : E ≠ ⊥)
    (hτ2empty : section12Tau2Primes M = ∅) :
    section14FrobeniusWithKernel M (section10Msigma M) := by
  classical
  have hxM : x ∈ M := section15_msigma_le hxMσ
  let Esub : Subgroup M := E.subgroupOf M
  have hcomp' : Esub.IsComplement' (section10MsigmaSubgroup M) :=
    section12_complement_to_msigma_isComplement' (M := M) (E := E) hcomp
  have hMsigma_ne : section10MsigmaSubgroup M ≠ ⊥ := by
    intro hbot
    have hxsub : (⟨x, hxM⟩ : M) ∈ section10MsigmaSubgroup M := by
      rw [← section15_msigma_subgroupOf_eq (M := M)]
      simpa [Subgroup.mem_subgroupOf] using hxMσ
    have hxbot : (⟨x, hxM⟩ : M) ∈ (⊥ : Subgroup M) := by
      simpa [hbot] using hxsub
    exact hxne (congrArg Subtype.val (Subgroup.mem_bot.mp hxbot))
  have hEsub_ne : Esub ≠ ⊥ := by
    intro hbot
    apply hEne
    apply le_bot_iff.mp
    intro e heE
    have heM : e ∈ M := hcomp.2.1 heE
    let eM : M := ⟨e, heM⟩
    have heSub : eM ∈ Esub := by
      simpa [Esub, eM, Subgroup.mem_subgroupOf] using heE
    have heBot : eM ∈ (⊥ : Subgroup M) := by
      simpa [hbot] using heSub
    change e = 1
    simpa [eM] using congrArg Subtype.val (Subgroup.mem_bot.mp heBot)
  refine ⟨section15_msigma_le (M := M), Esub, ?_⟩
  have hFrobSub :
      IsFrobeniusGroupWithKernelComplement (section10MsigmaSubgroup M) Esub := by
    refine
      (lemma_3_1 (G := M) (K := section10MsigmaSubgroup M) (R := Esub)
        hMsigma_ne hEsub_ne inferInstance hcomp'.symm).2 ?_
    intro e he_ne
    by_contra hCent_ne
    obtain ⟨y, hy_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCent_ne
    have hyCentMsub :
        ((y : elementCentralizerIn (section10MsigmaSubgroup M) (e : M)) : M) ∈
          (elementCentralizerIn (section10Msigma M) ((e : M) : G)).subgroupOf M := by
      have hyCentSub :
          ((y : elementCentralizerIn (section10MsigmaSubgroup M) (e : M)) : M) ∈
            elementCentralizerIn ((section10Msigma M).subgroupOf M) (e : M) := by
        simp [section15_msigma_subgroupOf_eq (M := M)]
      rw [section15_elementCentralizerIn_subgroupOf_eq
          (S := M) (H := section10Msigma M) (x := ((e : M) : G))
          (hx := (e : M).property)] at hyCentSub
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
      exact section12_not_sigma_of_mem_complement (G := G) hM hcomp hpE hpσ
    have heCent : ((e : M) : G) ∈ elementCentralizerIn M (y : G) := by
      refine ⟨(e : M).property, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_singleton_iff.mp hyCent.2).symm)
    have hcor :=
      corollary_14_3 (G := G) (M := M) (x := (y : G)) (x' := ((e : M) : G))
        hM hyMsigma hy_neG he_neG heCent he_sigma'
    obtain ⟨r, z, hzpow, _hzmem, _hzne, hzprime⟩ :=
      section15_exists_primeOrder_zpowers_in
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
      simp [hMFam.2] at hrκ
    · have hrτ2 : r ∈ section12Tau2Primes M := hτ2.1 hrSupp
      simp [hτ2empty] at hrτ2
  simpa [section15_msigma_subgroupOf_eq (M := M)] using hFrobSub

/-- Corollary 15.9 source core for parts (a)--(b): in the original
Theorem 14.4/Corollary 14.12 setup, the particular complement
`M ⊓ Mstar` supplied by Corollary 14.12 is cyclic, and `M` is Frobenius.

This is the explicit formal endpoint for the compressed source passage using
Theorem 15.8 and Theorem 15.7(d); the surrounding wrapper extracts the
complement and family data mechanically from Corollary 14.12. -/
private theorem CFSG.section15_corollary15_9_cyclic_frobenius_core
    {M N K U Mstar : Subgroup G} {x : G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (_hN : N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (_hNnotF : N ∉ section14MFamilyF G)
    (hr : r ∈ subgroupPrimeSet (Subgroup.zpowers x))
    (hInitial :
      N ∈ section14MFamilyP2 G ∧
        r ∈ section12Tau2Primes N ∧
          r ∈ section10SigmaPrimes M ∧
            section12ComplementIn N (section10Msigma N) (M ⊓ N))
    (hSituation : section15Corollary14_12Situation N M K Mstar U) :
    IsCyclic (M ⊓ Mstar : Subgroup G) ∧
      ∃ K : Subgroup G, section14FrobeniusWithKernel M K := by
  classical
  rcases hInitial with ⟨hNP2, hrτ2N, _hrσM, _hcompN⟩
  rcases section15_theorem15_8_corollary14_12_conclusions
      (G := G) (M := N) (H := M) (K := K) (Mstar := Mstar) (U := U)
      hSituation with
    ⟨hMFam, _hUleσM, _hNMprod, _hNormU_notN, _hKleF, hMcomp⟩
  have hNilMσ : Group.IsNilpotent (section10Msigma M) :=
    section15_msigma_nilpotent_of_mem_MFamilyF (G := G) (M := M) hMFam
  have hMFsub : section15MFSubgroup M (section10Msigma M) :=
    section15_msigma_MFSubgroup_of_nilpotent (G := G) (M := M) hM hNilMσ
  have hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M) :=
    section15_fitting_not_ti_of_MFamilyF_msigma_element
      (G := G) (M := M) (x := x) (r := r) hM hMFam hxMσ hxne hr hCGnot
  have hcompTo : section12ComplementToMsigma M (M ⊓ Mstar) := by
    simpa [section12ComplementToMsigma] using hMcomp
  rcases section15_exists_EData_for_fixed_sigma_complement
      (G := G) (M := M) (E := M ⊓ Mstar) hM hcompTo with
    ⟨E₁₂, E₁, E₂, E₃, hEdata⟩
  rcases section15_exists_MFSubgroup (G := G) Mstar with ⟨MFstar, hMFstar⟩
  rcases section15_cor14_12_situation_exists_prime_mem_K
      (G := G) hSituation with
    ⟨q, hqK⟩
  have hτ2empty : section12Tau2Primes M = ∅ := by
    by_contra hτ2Mne_empty
    have hτ2Mne : (section12Tau2Primes M).Nonempty := by
      exact Set.nonempty_iff_ne_empty.mpr hτ2Mne_empty
    have hτ2Nempty : section12Tau2Primes N = ∅ :=
      (theorem_15_8
        (G := G) (M := N) (H := M) (K := K) (Mstar := Mstar)
        (U := U) (MFstar := MFstar) (q := q)
        hSituation hMFstar hτ2Mne hqK).2.2
    simp [hτ2Nempty] at hrτ2N
  have hcyc : IsCyclic (M ⊓ Mstar : Subgroup G) :=
    section15_complement_cyclic_of_tau2_empty
      (G := G) (M := M) (E := M ⊓ Mstar) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (x := x)
      hM hMFam hMFsub hnotTI hxMσ hxne hCGnot hEdata hτ2empty
  have hEne : M ⊓ Mstar ≠ (⊥ : Subgroup G) :=
    section15_ne_bot_of_prime_mem_le_fitting
      (G := G) (E := M ⊓ Mstar) (K := K) (q := q) _hKleF hqK
  have hFrob :
      section14FrobeniusWithKernel M (section10Msigma M) :=
    section15_frobenius_msigma_of_tau2_empty
      (G := G) (M := M) (E := M ⊓ Mstar) (x := x)
      hM hMFam hxMσ hxne hcompTo hEne hτ2empty
  exact ⟨hcyc, ⟨section10Msigma M, hFrob⟩⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_isMulCommutative_of_le
    {H K : Subgroup G} (hH : IsMulCommutative H) (hKH : K ≤ H) :
    IsMulCommutative K := by
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  exact setLike_mul_comm (s := H)
    (hKH x.property) (hKH y.property)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_subgroupCentralizerIn_eq_bot_of_regular
    {X R : Subgroup G}
    (hXne : X ≠ ⊥)
    (hreg : section14ActsRegularlyOn X R) :
    subgroupCentralizerIn R X = ⊥ := by
  classical
  apply le_bot_iff.mp
  intro y hy
  haveI : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot (H := X)).2 hXne
  obtain ⟨xX, hxXne⟩ := exists_ne (1 : X)
  let x : G := xX
  have hxX : x ∈ X := xX.property
  have hxne : x ≠ 1 := by
    intro hx
    exact hxXne (Subtype.ext hx)
  have hyElem : y ∈ elementCentralizerIn R x := by
    refine ⟨hy.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr <| by
      exact (Subgroup.mem_centralizer_iff.mp hy.2 x hxX).symm
  simpa [hreg.2 x hxX hxne] using hyElem

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_normalizer_le_normalizer_centralizer
    (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hxn : n⁻¹ * x * n ∈ X := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (X : Set G)).inv_mem hn) x).1 hx
    have hcomm : (n⁻¹ * x * n) * c = c * (n⁻¹ * x * n) := hc _ hxn
    have hcomm' := congrArg (fun y : G => n * y * n⁻¹) hcomm
    simpa [mul_assoc] using hcomm'
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hxn : n * x * n⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hn x).1 hx
    have hcomm :
        (n * x * n⁻¹) * (n * c * n⁻¹) =
          (n * c * n⁻¹) * (n * x * n⁻¹) :=
      hc _ hxn
    have hcomm' := congrArg (fun y : G => n⁻¹ * y * n) hcomm
    simpa [mul_assoc] using hcomm'

private theorem CFSG.section15_normalizer_le_of_unique_centralizer_primeOrder
    {M A X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hX : X ∈ section12PrimeOrderSubgroups A)
    (huniq : section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  classical
  have hCX_le_M : Subgroup.centralizer (X : Set G) ≤ M := by
    have hMmem :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
      rw [huniq]
      simp
    exact hMmem.2
  have hNCX_ne_top :
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) ≠ ⊤ := by
    intro hNCXtop
    have hCXnormal : (Subgroup.centralizer (X : Set G)).Normal :=
      Subgroup.normalizer_eq_top_iff.mp hNCXtop
    letI : IsSimpleGroup G := IsMinCE.simple
    rcases hCXnormal.eq_bot_or_eq_top with hCXbot | hCXtop
    · have hXne : X ≠ ⊥ := by
        rcases hX with ⟨_hXA, p, hXcard⟩
        intro hXbot
        have hcard_bot : Nat.card X = 1 := (Subgroup.card_eq_one (H := X)).2 hXbot
        have hp_one : p.val = 1 := hXcard.symm.trans hcard_bot
        exact (Nat.Prime.ne_one p.property) hp_one
      haveI : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot (H := X)).2 hXne
      obtain ⟨x, hxX, hxne⟩ := Subgroup.exists_ne_one_of_nontrivial X
      rcases hX with ⟨_hXA, p, hXcard⟩
      have hXle_zpow : X ≤ Subgroup.zpowers x := by
        intro y hyX
        haveI : Fact p.val.Prime := ⟨p.2⟩
        have hySub :
            (⟨y, hyX⟩ : X) ∈ Subgroup.zpowers (⟨x, hxX⟩ : X) :=
          mem_zpowers_of_prime_card
            (G := X) (p := p.val) (by simpa using hXcard)
            (g := (⟨x, hxX⟩ : X)) (g' := (⟨y, hyX⟩ : X))
            (by simpa using hxne)
        rcases Subgroup.mem_zpowers_iff.mp hySub with ⟨n, hn⟩
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩
      letI : IsMulCommutative X :=
        section15_isMulCommutative_of_le
          (H := Subgroup.zpowers x) (K := X) (Subgroup.zpowers_isMulCommutative x)
          hXle_zpow
      have hXle_CX : X ≤ Subgroup.centralizer (X : Set G) :=
        Subgroup.le_centralizer X
      have hXbot : X = ⊥ := by
        apply le_bot_iff.mp
        simpa [hCXbot] using hXle_CX
      exact hXne hXbot
    · exact hM.1 (top_le_iff.mp (hCXtop ▸ hCX_le_M))
  have hNCX_le_M :
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) ≤ M := by
    obtain ⟨N, hN⟩ :=
      section9_exists_maximalSubgroupsContaining_of_ne_top
        (G := G) (H := Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G))
        hNCX_ne_top
    have hNcontCX :
        N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
      exact ⟨hN.1, Subgroup.le_normalizer.trans hN.2⟩
    have hNeqM : N = M := by
      have hNmem : N ∈ ({M} : Set (Subgroup G)) := by
        simpa [huniq] using hNcontCX
      simpa using hNmem
    exact hNeqM ▸ hN.2
  exact (section15_normalizer_le_normalizer_centralizer (G := G) X).trans hNCX_le_M

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_centralizer_singleton_le_centralizer_zpowers_of_mem
    {x y : G} (hyx : y ∈ Subgroup.zpowers x) :
    Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
  intro g hg
  have hgx : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hgy : Commute g y := by
    rcases Subgroup.mem_zpowers_iff.mp hyx with ⟨n, hn⟩
    rw [← hn]
    exact hgx.zpow_right n
  exact section15_centralizer_singleton_le_centralizer_zpowers
    (G := G) (a := y) (Subgroup.mem_centralizer_singleton_iff.mpr hgy)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_elementCentralizerIn_le_subgroupCentralizerIn_zpowers_of_mem
    {Q : Subgroup G} {x y : G} (hyx : y ∈ Subgroup.zpowers x) :
    elementCentralizerIn Q x ≤ subgroupCentralizerIn Q (Subgroup.zpowers y) := by
  intro g hg
  exact ⟨hg.1, section15_centralizer_singleton_le_centralizer_zpowers_of_mem
    (G := G) hyx hg.2⟩

/-- The strengthened internal package for the exact complement used in
Corollary 15.9: it remembers the witnesses `K₁,U₁,M*` from the source
construction, not just the final (a)--(b) conclusions. -/
private def CFSG.section15Corollary15_9ChosenComplementData
    (M N E : Subgroup G) (r : Nat.Primes) : Prop :=
  ∃ K U Mstar : Subgroup G,
    section12HallSubgroupIn (section14KappaPrimes N) K N ∧
      K ≤ M ⊓ N ∧
        K ≤ E ∧
          U ≤ M ⊓ N ∧
            section14Proposition14_2AData N K U ∧
                section14Theorem14_7Data N K Mstar ∧
                  section15Corollary14_12Situation N M K Mstar U ∧
                    ((N ⊓ M : Subgroup G) : Set G) = (U : Set G) * (K : Set G) ∧
                      E = M ⊓ Mstar ∧
                        section12ComplementToMsigma M E ∧
                          M ∈ section14MFamilyF G ∧
                            N ∈ section14MFamilyP2 G ∧
                              IsCyclic E ∧
                                (∃ K₀ : Subgroup G, section14FrobeniusWithKernel M K₀) ∧
                                  r ∈ section12Tau2Primes N

omit [IsMinCE G] in
private theorem CFSG.section15_corollary15_9ChosenComplementData_conclusions
    {M N E : Subgroup G} {r : Nat.Primes}
    (hChosen : section15Corollary15_9ChosenComplementData M N E r) :
    section12ComplementToMsigma M E ∧
      M ∈ section14MFamilyF G ∧
        N ∈ section14MFamilyP2 G ∧
          IsCyclic E ∧
            (∃ K : Subgroup G, section14FrobeniusWithKernel M K) ∧
              r ∈ section12Tau2Primes N := by
  rcases hChosen with
    ⟨K, U, Mstar, _hK, _hKleMN, _hKleE, _hUleMN, _hU, _h14, _hSituation,
      _hProd, _hEeq, hEcomp, hMF, hNP2, hcyc, hFrob, hrτ2⟩
  exact ⟨hEcomp, hMF, hNP2, hcyc, hFrob, hrτ2⟩

private theorem CFSG.section15_corollary15_9_zpowers_le_prop14_U
    {M N K U : Subgroup G} {x xᵣ : G} {r : Nat.Primes}
    (hxMσ : x ∈ section10Msigma M)
    (hN : N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hxᵣmem : xᵣ ∈ Subgroup.zpowers x)
    (hxᵣorder : orderOf xᵣ = r.val)
    (hrτ2 : r ∈ section12Tau2Primes N)
    (hK : section12HallSubgroupIn (section14KappaPrimes N) K N)
    (hU : section14Proposition14_2AData N K U)
    (hprod : ((N ⊓ M : Subgroup G) : Set G) = (U : Set G) * (K : Set G)) :
    Subgroup.zpowers xᵣ ≤ U := by
  classical
  rcases hU with ⟨_hprime, _hcomm, hUHall, hreg, _hnormComp⟩
  have hxM : x ∈ M := (section15_msigma_le (M := M)) hxMσ
  have hxN : x ∈ N := by
    apply hN.2
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy_eq : y = x := by simpa using hy
    simp [hy_eq]
  have hxᵣM : xᵣ ∈ M := (Subgroup.zpowers_le.2 hxM) hxᵣmem
  have hxᵣN : xᵣ ∈ N := (Subgroup.zpowers_le.2 hxN) hxᵣmem
  have hxᵣNM : xᵣ ∈ N ⊓ M := ⟨hxᵣN, hxᵣM⟩
  have hxᵣUKset : xᵣ ∈ (U : Set G) * (K : Set G) := by
    have hxᵣNMset : xᵣ ∈ ((N ⊓ M : Subgroup G) : Set G) := hxᵣNM
    rw [hprod] at hxᵣNMset
    exact hxᵣNMset
  have hUK_mul :
      ((U ⊔ K : Subgroup G) : Set G) = (U : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (N := U) (H := K) hreg.1
  have hxᵣKU : xᵣ ∈ K ⊔ U := by
    have hxᵣUK : xᵣ ∈ U ⊔ K := by
      have hxᵣUKset' := hxᵣUKset
      rw [← hUK_mul] at hxᵣUKset'
      exact hxᵣUKset'
    simpa [sup_comm] using hxᵣUK
  let X : Subgroup G := Subgroup.zpowers xᵣ
  have hXKU : X ≤ K ⊔ U := Subgroup.zpowers_le.2 hxᵣKU
  have hKUdata : section15KUData N K U :=
    section15_KUData_of_proposition14_2AData
      (G := G) (M := N) (K := K) (U := U) hN.1 hK
      ⟨_hprime, _hcomm, hUHall, hreg, _hnormComp⟩
  have hUnormKU : section10NormalIn U (K ⊔ U) :=
    hKUdata.2.2.2.2.2.2
  haveI : (U.subgroupOf (K ⊔ U)).Normal := hUnormKU.2
  let π : Set Nat.Primes := (section14KappaPrimes N ∪ section10SigmaPrimes N)ᶜ
  have hUHallKU : section12HallSubgroupIn π U (K ⊔ U) := by
    exact section15_hallSubgroupIn_of_le_overgroup
      (G := G) (M := N) (E := K ⊔ U) (U := U) (π := π)
      hUHall le_sup_right (sup_le hK.1 hUHall.1)
  have hrπ : r ∈ π := by
    intro hrκσ
    rcases hrκσ with hrκ | hrσ
    · exact section15_tau2_not_mem_kappa (G := G) (M := N) hrτ2 hrκ
    · exact hrτ2.1 hrσ
  have hXp : IsPGroup r.val (X.subgroupOf (K ⊔ U)) := by
    haveI : Fact r.val.Prime := ⟨r.property⟩
    have hXpG : IsPGroup r.val X := by
      refine IsPGroup.of_card (p := r.val) (G := X) (n := 1) ?_
      simp [X, hxᵣorder, pow_one]
    exact hXpG.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := K ⊔ U) hXKU).symm
  have hXUsub : X.subgroupOf (K ⊔ U) ≤ U.subgroupOf (K ⊔ U) :=
    section15_pSubgroup_le_normal_hall_of_prime_mem
      (R := ↥(K ⊔ U : Subgroup G)) (π := π) (H := U.subgroupOf (K ⊔ U))
      (A := X.subgroupOf (K ⊔ U)) hUHallKU.2 hrπ hXp
  intro y hyX
  let yKU : ↥(K ⊔ U : Subgroup G) := ⟨y, hXKU hyX⟩
  have hyXsub : yKU ∈ X.subgroupOf (K ⊔ U) := by
    simpa [yKU, Subgroup.mem_subgroupOf, X] using hyX
  have hyUsub : yKU ∈ U.subgroupOf (K ⊔ U) := hXUsub hyXsub
  simpa [yKU, Subgroup.mem_subgroupOf] using hyUsub

private theorem CFSG.section15_corollary15_9_zpowers_centralizer_nontrivial
    {M N : Subgroup G} {x xᵣ : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (hN : N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (hxᵣmem : xᵣ ∈ Subgroup.zpowers x) :
    subgroupCentralizerIn (section10Msigma N) (Subgroup.zpowers xᵣ) ≠ ⊥ := by
  classical
  have hMx : M ∈ section14MsigmaElement x :=
    section15_corollary15_9_msigma_member (G := G) hM hxMσ
  have hNdataM :=
    section15_corollary15_9_theorem14_4_data
      (G := G) hM hxMσ hxne hN hCGnot M hMx
  rcases hNdataM with
    ⟨hR_eq, hRne, _hcent, _hSupp_tau2N, _hTau2N_le_sigmaM,
      _hbetaN, _hcompN, _hNF_or_P2⟩
  have hRle :
      section14R x ≤ subgroupCentralizerIn (section10Msigma N) (Subgroup.zpowers xᵣ) := by
    intro y hyR
    have hyElem : y ∈ elementCentralizerIn (section10Msigma N) x := by
      simpa [hR_eq] using hyR
    exact section15_elementCentralizerIn_le_subgroupCentralizerIn_zpowers_of_mem
      (G := G) (Q := section10Msigma N) hxᵣmem hyElem
  intro hbot
  have hRbot : section14R x = ⊥ := by
    apply le_bot_iff.mp
    intro y hyR
    simpa [hbot] using hRle hyR
  exact hRne hRbot

/-- Corollary 15.9 source bridge for the exact complement chosen in the
source proof, after the Theorem 14.4 initial data has already been
extracted. -/
private theorem CFSG.section15_corollary15_9_exists_chosen_complement_for_ab_of_initial_data
    {M N : Subgroup G} {x xᵣ : G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (hN : N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNnotF : N ∉ section14MFamilyF G)
    (hr : r ∈ subgroupPrimeSet (Subgroup.zpowers x))
    (_hxᵣmem : xᵣ ∈ Subgroup.zpowers x)
    (_hxᵣorder : orderOf xᵣ = r.val)
    (hInitial :
      N ∈ section14MFamilyP2 G ∧
        r ∈ section12Tau2Primes N ∧
          r ∈ section10SigmaPrimes M ∧
            section12ComplementIn N (section10Msigma N) (M ⊓ N)) :
    ∃ E : Subgroup G, section15Corollary15_9ChosenComplementData M N E r := by
  classical
  have hInitialFull := hInitial
  rcases hInitial with ⟨hNP2, _hrτ2, _hrσM, hcompN⟩
  rcases section15_exists_kappa_hallSubgroupIn_le_sigma_complement
      (G := G) (M := M) (N := N) hNP2.1.1 hcompN with
    ⟨K₁, hK₁, hK₁leMN⟩
  have hcompToN : section12ComplementToMsigma N (M ⊓ N) := by
    simpa [section12ComplementToMsigma] using hcompN
  rcases proposition_14_2_a_of_fixed_sigma_complement
      (G := G) (M := N) (K := K₁) (E := M ⊓ N) hNP2.1 hK₁ hcompToN hK₁leMN with
    ⟨U₁, hU₁leMN, hU₁⟩
  let Mstar : Subgroup G := section14Theorem14_7Partner N K₁
  have h14 : section14Theorem14_7Data N K₁ Mstar := by
    simpa [Mstar] using theorem_14_7_data (G := G) (M := N) (K := K₁) hNP2.1 hK₁
  have hSituation : section15Corollary14_12Situation N M K₁ Mstar U₁ :=
    section15_corollary15_9_cor14_12_situation
      (G := G) (M := M) (N := N) (K := K₁) (U := U₁) (Mstar := Mstar) (r := r)
      hM hInitialFull hK₁ hK₁leMN hU₁leMN hU₁ h14
  rcases section15_theorem15_8_corollary14_12_conclusions
      (G := G) (M := N) (H := M) (K := K₁) (Mstar := Mstar) (U := U₁)
      hSituation with
    ⟨hMF, _hUleσM, hNMprod, _hNormU_notN, hKleF, hMcomp⟩
  rcases section15_corollary15_9_cyclic_frobenius_core
      (G := G) (M := M) (N := N) (K := K₁) (U := U₁) (Mstar := Mstar)
      (x := x) (r := r)
      hM hxMσ hxne hN hCGnot hNnotF hr hInitialFull hSituation with
    ⟨hcyc, hFrob⟩
  have hK₁leE : K₁ ≤ M ⊓ Mstar :=
    hKleF.trans (section8FittingSubgroup_le (M ⊓ Mstar))
  refine
    ⟨M ⊓ Mstar, K₁, U₁, Mstar, hK₁, hK₁leMN, hK₁leE, hU₁leMN, hU₁,
      h14, hSituation, hNMprod, rfl, ?_, hMF, hNP2, hcyc, hFrob, ?_⟩
  · simpa [section12ComplementToMsigma] using hMcomp
  · exact hInitialFull.2.1


omit [IsMinCE G] in
private theorem CFSG.section15_corollary15_9_inter_eq_k_of_chosen_factors
    {M N E K U : Subgroup G}
    (hNP2 : N ∈ section14MFamilyP2 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes N) K N)
    (hKleMN : K ≤ M ⊓ N)
    (hKleE : K ≤ E)
    (hU : section14Proposition14_2AData N K U)
    (hprod : ((N ⊓ M : Subgroup G) : Set G) = (U : Set G) * (K : Set G))
    (hEcomp : section12ComplementToMsigma M E)
    (hEcyc : IsCyclic E) :
    E ⊓ N = K := by
  classical
  apply le_antisymm
  · intro y hy
    have hyE : y ∈ E := hy.1
    have hyN : y ∈ N := hy.2
    have hyM : y ∈ M := hEcomp.2.1 hyE
    have hyNM : y ∈ N ⊓ M := ⟨hyN, hyM⟩
    have hyProd : y ∈ (U : Set G) * (K : Set G) := by
      have hyNMset : y ∈ ((N ⊓ M : Subgroup G) : Set G) := hyNM
      rw [hprod] at hyNMset
      exact hyNMset
    rw [Set.mem_mul] at hyProd
    rcases hyProd with ⟨u, huU, k, hkK, huk⟩
    rcases hU with ⟨_hprime, _hcomm, _hUHall, hreg, _hnormComp⟩
    have hKne : K ≠ ⊥ := section15_hall_kappa_ne_bot hNP2.1 hK
    have hCUK_bot : subgroupCentralizerIn U K = ⊥ :=
      section15_subgroupCentralizerIn_eq_bot_of_regular hKne hreg
    have hEcomm : IsMulCommutative E := by
      letI : IsCyclic E := hEcyc
      infer_instance
    have huE : u ∈ E := by
      have hu_eq : u = y * k⁻¹ := by
        rw [← huk]
        simp [mul_assoc]
      rw [hu_eq]
      exact E.mul_mem hyE (E.inv_mem (hKleE hkK))
    have huCent : u ∈ subgroupCentralizerIn U K := by
      refine ⟨huU, ?_⟩
      change u ∈ Subgroup.centralizer (K : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro a haK
      exact setLike_mul_comm
        (s := E) (hKleE haK) huE
    have huBot : u ∈ (⊥ : Subgroup G) := by
      simpa [hCUK_bot] using huCent
    have huOne : u = 1 := by
      simpa using huBot
    have hy_eq_k : y = k := by
      calc
        y = u * k := huk.symm
        _ = k := by simp [huOne]
    simpa [hy_eq_k] using hkK
  · intro y hyK
    exact ⟨hKleE hyK, (hKleMN hyK).2⟩

/-- Corollary 15.9 source bridge for part (c): Theorem 15.1, applied to
the same complement `E` chosen in parts (a)--(b), gives the normalizer
containment and cardinality endpoint. -/
private theorem CFSG.section15_corollary15_9_theorem15_1_endpoint
    {M N E : Subgroup G} {x xᵣ : G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (hN : N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (_hNnotF : N ∉ section14MFamilyF G)
    (_hr : r ∈ subgroupPrimeSet (Subgroup.zpowers x))
    (hxᵣmem : xᵣ ∈ Subgroup.zpowers x)
    (hxᵣorder : orderOf xᵣ = r.val)
    (_hInitial :
      N ∈ section14MFamilyP2 G ∧
        r ∈ section12Tau2Primes N ∧
          r ∈ section10SigmaPrimes M ∧
            section12ComplementIn N (section10Msigma N) (M ⊓ N))
    (hChosen : section15Corollary15_9ChosenComplementData M N E r) :
    subgroupNormalizerIn E (Subgroup.zpowers xᵣ : Set G) ≤ E ⊓ N ∧
      Nat.card (E ⊓ N : Subgroup G) = (ambientDerivedSubgroup N).relIndex N := by
  classical
  rcases hChosen with
    ⟨K, U, Mstar, hK, hKleMN, hKleE, hUleMN, hU, _h14, _hSituation,
      hprod, _hEeq, hEcomp, _hMF, hNP2, hEcyc, _hFrob, hrτ2⟩
  let X : Subgroup G := Subgroup.zpowers xᵣ
  have hXU : X ≤ U :=
    section15_corollary15_9_zpowers_le_prop14_U
      (G := G) (M := M) (N := N) (K := K) (U := U)
      (x := x) (xᵣ := xᵣ) (r := r)
      hxMσ hN hxᵣmem hxᵣorder hrτ2 hK hU hprod
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hcard_bot : Nat.card X = 1 := (Subgroup.card_eq_one (H := X)).2 hbot
    have hcard_prime : Nat.card X = r.val := by
      simp [X, hxᵣorder]
    have hr_one : r.val = 1 := hcard_prime.symm.trans hcard_bot
    exact (Nat.Prime.ne_one r.property) hr_one
  have hCentNe :
      subgroupCentralizerIn (section10Msigma N) X ≠ ⊥ := by
    simpa [X] using
      section15_corollary15_9_zpowers_centralizer_nontrivial
        (G := G) (M := M) (N := N) (x := x) (xᵣ := xᵣ)
        hM hxMσ hxne hN hCGnot hxᵣmem
  have hKU : section15KUData N K U :=
    section15_KUData_of_proposition14_2AData
      (G := G) (M := N) (K := K) (U := U) hNP2.1.1 hK hU
  have h151c :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {N} ∧
        IsCyclic X ∧ IsPiSubgroup (G := G) (section12Tau2Primes N) X :=
    lemma_15_1_c (G := G) (M := N) (K := K) (U := U) (X := X)
      hNP2.1.1 hKU hXU hXne hCentNe
  have hXleN : X ≤ N := hXU.trans hU.2.2.1.1
  have hXprime : X ∈ section12PrimeOrderSubgroups N := by
    exact ⟨hXleN, ⟨r, by simp [X, hxᵣorder]⟩⟩
  have hNormalizer_le_N : Subgroup.normalizer (X : Set G) ≤ N :=
    section15_normalizer_le_of_unique_centralizer_primeOrder
      (G := G) (M := N) (A := N) (X := X) hNP2.1.1 hXprime h151c.1
  have hNormalizerIn :
      subgroupNormalizerIn E (X : Set G) ≤ E ⊓ N := by
    intro g hg
    have hg' : g ∈ Subgroup.normalizer (X : Set G) ⊓ E := by
      simpa [subgroupNormalizerIn] using hg
    exact ⟨hg'.2, hNormalizer_le_N hg'.1⟩
  have hENeqK : E ⊓ N = K :=
    section15_corollary15_9_inter_eq_k_of_chosen_factors
      (G := G) (M := M) (N := N) (E := E) (K := K) (U := U)
      hNP2 hK hKleMN hKleE hU hprod hEcomp hEcyc
  let D : Subgroup G := ambientDerivedSubgroup N
  have hDcomp : section12ComplementIn N K D := by
    simpa [D] using theorem_14_7_h (G := G) (M := N) (K := K) hNP2.1 hK
  have hDnorm : section10NormalIn D N := by
    simpa [D] using section15_ambientDerived_normalIn (M := N)
  have hcompSub :
      (K.subgroupOf N).IsComplement' (D.subgroupOf N) :=
    section15_normal_complementIn_isComplement' hDcomp hDnorm
  have hcardK :
      Nat.card K = (ambientDerivedSubgroup N).relIndex N := by
    calc
      Nat.card K = Nat.card (K.subgroupOf N) := by
        exact (section12_card_subgroupOf_eq hK.1).symm
      _ = (D.subgroupOf N).index := by
        exact hcompSub.index_eq_card.symm
      _ = (ambientDerivedSubgroup N).relIndex N := by
        rfl
  have hcardEN :
      Nat.card (E ⊓ N : Subgroup G) =
        (ambientDerivedSubgroup N).relIndex N := by
    simpa [hENeqK] using hcardK
  constructor
  · simpa [X] using hNormalizerIn
  · exact hcardEN

/-- Corollary 15.9 source bridge for part (c): after the original source
context and the same suitable complement package are available, delegate to
the explicit Theorem 15.1 endpoint. -/
private theorem CFSG.section15_corollary15_9_part_c_source
    {M N E : Subgroup G} {x xᵣ : G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (hN : N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNnotF : N ∉ section14MFamilyF G)
    (hr : r ∈ subgroupPrimeSet (Subgroup.zpowers x))
    (hxᵣmem : xᵣ ∈ Subgroup.zpowers x)
    (hxᵣorder : orderOf xᵣ = r.val)
    (hInitial :
      N ∈ section14MFamilyP2 G ∧
        r ∈ section12Tau2Primes N ∧
          r ∈ section10SigmaPrimes M ∧
            section12ComplementIn N (section10Msigma N) (M ⊓ N))
    (hChosen : section15Corollary15_9ChosenComplementData M N E r) :
    subgroupNormalizerIn E (Subgroup.zpowers xᵣ : Set G) ≤ E ⊓ N ∧
      Nat.card (E ⊓ N : Subgroup G) = (ambientDerivedSubgroup N).relIndex N := by
  exact
    section15_corollary15_9_theorem15_1_endpoint
      hM hxMσ hxne hN hCGnot hNnotF hr hxᵣmem hxᵣorder hInitial hChosen

/-- Corollary 15.9 source block (c): for the same complement `E` chosen in
(a)--(b), Theorem 15.1 applied inside the `K₁U₁` decomposition gives the
normalizer containment and the displayed cardinality. -/
private theorem CFSG.section15_corollary15_9_part_c_for_complement
    {M N E : Subgroup G} {x xᵣ : G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (hN : N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNnotF : N ∉ section14MFamilyF G)
    (hr : r ∈ subgroupPrimeSet (Subgroup.zpowers x))
    (hxᵣmem : xᵣ ∈ Subgroup.zpowers x)
    (hxᵣorder : orderOf xᵣ = r.val)
    (hChosen : section15Corollary15_9ChosenComplementData M N E r) :
    subgroupNormalizerIn E (Subgroup.zpowers xᵣ : Set G) ≤ E ⊓ N ∧
      Nat.card (E ⊓ N : Subgroup G) = (ambientDerivedSubgroup N).relIndex N := by
  exact
    section15_corollary15_9_part_c_source
      hM hxMσ hxne hN hCGnot hNnotF hr hxᵣmem hxᵣorder
      (section15_corollary15_9_initial_data
        hM hxMσ hxne hN hCGnot hNnotF hr)
      hChosen

/-- Corollary 15.9: under the stated hypotheses on
`x ∈ M_σ#`, `N ∈ 𝓜(C_G(x))`, `r ∈ π(⟨x⟩)`, and an element `x_r` of
order `r`, there is a suitable complement `E` for which parts (a)--(c)
hold. -/
public theorem CFSG.corollary_15_9
    {M N : Subgroup G} {x xᵣ : G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (hN : N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNnotF : N ∉ section14MFamilyF G)
    (hr : r ∈ subgroupPrimeSet (Subgroup.zpowers x))
    (hxᵣmem : xᵣ ∈ Subgroup.zpowers x)
    (hxᵣorder : orderOf xᵣ = r.val) :
    ∃ E : Subgroup G, section15Corollary15_9Conclusions M N E r xᵣ := by
  rcases section15_corollary15_9_exists_chosen_complement_for_ab_of_initial_data
      hM hxMσ hxne hN hCGnot hNnotF hr hxᵣmem hxᵣorder
      (section15_corollary15_9_initial_data
        hM hxMσ hxne hN hCGnot hNnotF hr) with
    ⟨E, hChosen⟩
  have hEpack :=
    section15_corollary15_9ChosenComplementData_conclusions
      (G := G) (M := M) (N := N) (E := E) (r := r) hChosen
  rcases hEpack with
    ⟨hcomp, hMFam, hNP2, hcyc, hfrob, hrTau⟩
  have hc :
      subgroupNormalizerIn E (Subgroup.zpowers xᵣ : Set G) ≤ E ⊓ N ∧
        Nat.card (E ⊓ N : Subgroup G) =
          (ambientDerivedSubgroup N).relIndex N := by
    exact
      section15_corollary15_9_part_c_for_complement
        hM hxMσ hxne hN hCGnot hNnotF hr hxᵣmem hxᵣorder
        hChosen
  exact ⟨E, hcomp, hMFam, hNP2, hcyc, hfrob, hrTau, hc.1, hc.2⟩

end Section15
