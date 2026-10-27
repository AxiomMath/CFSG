module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_2_d
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Theorem 10.2(e) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section10_not_isCyclic_min_ce :
    ¬ IsCyclic G := by
  intro hcyc
  letI : IsCyclic G := hcyc
  letI : CommGroup G := IsCyclic.commGroup
  exact IsMinCE.not_solvable (G := G) (isSolvable_of_comm (fun a b : G => mul_comm a b))

private theorem CFSG.section10_maximalSubgroup_ne_bot
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    M ≠ ⊥ := by
  classical
  intro hMbot
  have htop_le_bot : (⊤ : Subgroup G) ≤ (⊥ : Subgroup G) := by
    intro g _hg
    by_cases hgcyc : Subgroup.zpowers g = ⊤
    · exact False.elim <|
        section10_not_isCyclic_min_ce
          ((isCyclic_iff_exists_zpowers_eq_top (α := G)).2 ⟨g, hgcyc⟩)
    · have hzg_eq_M : Subgroup.zpowers g = M :=
        (hM.le_iff_eq hgcyc).mp (by simp [hMbot])
      have hgM : g ∈ M := by
        simpa [hzg_eq_M] using (Subgroup.mem_zpowers g)
      simpa [hMbot] using hgM
  have hbot_top : (⊥ : Subgroup G) = ⊤ := top_le_iff.mp htop_le_bot
  exact section10_not_isCyclic_min_ce <| by
    refine (isCyclic_iff_exists_zpowers_eq_top (α := G)).2 ⟨1, ?_⟩
    simp [hbot_top]

omit [IsMinCE G] in
private theorem CFSG.section10_groupRank_le_of_quotient_bot
    {H : Type*} [Group H] [Finite H] {K : Subgroup H} [K.Normal]
    (hK : K = ⊥) :
    groupRank H ≤ groupRank (H ⧸ K) := by
  let e : H ⧸ K ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hK).trans QuotientGroup.quotientBot
  exact section10_groupRank_le_of_equiv_pre (R := H ⧸ K) (S := H) e

omit [IsMinCE G] in
public theorem CFSG.section10_exists_largest_prime_divisor_of_nontrivial
    (H : Type*) [Group H] [Finite H] [Nontrivial H] :
    ∃ q : Nat.Primes, IsLargestPrimeDivisor q.val (Nat.card H) := by
  classical
  have hcard_gt : 1 < Nat.card H :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hpf_nonempty : (Nat.card H).primeFactors.Nonempty := by
    simpa using (Nat.nonempty_primeFactors (n := Nat.card H)).2 hcard_gt
  let q0 := (Nat.card H).primeFactors.max' hpf_nonempty
  have hq0_mem : q0 ∈ (Nat.card H).primeFactors := Finset.max'_mem _ _
  refine ⟨⟨q0, Nat.prime_of_mem_primeFactors hq0_mem⟩, ?_, ?_, ?_⟩
  · exact Nat.prime_of_mem_primeFactors hq0_mem
  · exact Nat.dvd_of_mem_primeFactors hq0_mem
  · intro r hr hrdvd
    have hr_mem : r ∈ (Nat.card H).primeFactors :=
      Nat.Prime.mem_primeFactors hr hrdvd Nat.card_pos.ne'
    exact Finset.le_max' _ _ hr_mem

omit [IsMinCE G] in
omit [Finite G] in
public theorem CFSG.section10_map_subtype_ne_bot_of_ne_bot
    {M : Subgroup G} {K : Subgroup M} (hK : K ≠ ⊥) :
    K.map M.subtype ≠ (⊥ : Subgroup G) := by
  intro hmap
  have hmap_bot : K.map M.subtype = (⊥ : Subgroup M).map M.subtype := by
    simpa using hmap
  exact hK ((Subgroup.map_injective M.subtype_injective) hmap_bot)

public theorem CFSG.section10_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (N : Subgroup M) [N.Normal] (hNne : N ≠ ⊥) :
    Subgroup.normalizer (((N : Subgroup M).map M.subtype : Subgroup G) : Set G) = M := by
  have hM8 : M ∈ section8MaximalSubgroups G := by
    simpa [section8MaximalSubgroups, section9MaximalSubgroups] using hM
  simpa [section8SubgroupInAmbient] using
    (section8_normalizer_subgroupInAmbient_eq_of_nontrivial_normal_in_maximal
      (G := G) (M := M) hM8 (K := N) hNne (by infer_instance))

public theorem CFSG.section10_exists_sigma_prime_of_malpha_eq_bot
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hα : section10MalphaSubgroup M = ⊥) :
    ∃ q : Nat.Primes, q ∈ section10SigmaPrimes M ∧ q.val ∣ Nat.card M := by
  classical
  have hMne : M ≠ ⊥ := section10_maximalSubgroup_ne_bot hM
  haveI : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hMne
  have hMsolv : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hModd : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hMrank : groupRank M ≤ 2 :=
    (section10_groupRank_le_of_quotient_bot
      (H := M) (K := section10MalphaSubgroup M) hα).trans
      (theorem_10_2_d hM).1
  obtain ⟨n, series, primes, htop, hbot, hchar, _hmono, hfac⟩ :=
    theorem_4_20_c (G := M) hMsolv hModd (Or.inl hMrank)
  let Bad : ℕ → Prop := fun k => ∃ hk : k < n + 1, series ⟨k, hk⟩ = ⊥
  have hBad_exists : ∃ k, Bad k := by
    refine ⟨n, ?_⟩
    refine ⟨Nat.lt_succ_self n, ?_⟩
    change series (Fin.last n) = ⊥
    exact hbot
  let k : ℕ := Nat.find hBad_exists
  have hkBad : Bad k := Nat.find_spec hBad_exists
  rcases hkBad with ⟨hk_lt, hk_bot⟩
  have hk_le_n : k ≤ n := Nat.lt_succ_iff.mp hk_lt
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have htop_bot : (⊤ : Subgroup M) = ⊥ := by
      calc
        (⊤ : Subgroup M) = series 0 := htop.symm
        _ = series ⟨k, hk_lt⟩ := by
          have hidx : (0 : Fin (n + 1)) = ⟨k, hk_lt⟩ := by
            ext
            simp [hk0]
          rw [hidx]
        _ = ⊥ := hk_bot
    exact (top_ne_bot : (⊤ : Subgroup M) ≠ ⊥) htop_bot
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne_zero
  let i : Fin n := ⟨k - 1, by omega⟩
  have hi_succ : i.succ = (⟨k, hk_lt⟩ : Fin (n + 1)) := by
    ext
    simp [i]
    omega
  have hi_cast :
      i.castSucc = (⟨k - 1, by omega⟩ : Fin (n + 1)) := by
    ext
    simp [i]
  have hsucc_bot : series i.succ = ⊥ := by
    simpa [hi_succ] using hk_bot
  have hcast_ne_bot : series i.castSucc ≠ ⊥ := by
    intro hcast_bot
    have hBad_pred : Bad (k - 1) := by
      refine ⟨by omega, ?_⟩
      simpa [hi_cast] using hcast_bot
    have hmin : k ≤ k - 1 := Nat.find_min' hBad_exists hBad_pred
    omega
  rcases hfac i with ⟨hle, hprime, S0, _hnormal_lower, hnonempty⟩
  haveI : Fact (Nat.Prime (primes i)) := hprime
  let U : Subgroup M := series i.castSucc
  let L : Subgroup U := (series i.succ).subgroupOf U
  have hL_bot : L = ⊥ := by
    ext x
    simp [L, U, hsucc_bot]
  rcases hnonempty with ⟨e⟩
  have hquot_card :
      Nat.card (U ⧸ L) = Nat.card (S0 : Subgroup M) :=
    Nat.card_congr e.toEquiv
  have hU_card_quot : Nat.card U = Nat.card (U ⧸ L) := by
    have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup L
    have hL_card : Nat.card L = 1 := by simp [hL_bot]
    simpa [hL_card] using hlag
  have hU_card :
      Nat.card U = (primes i) ^ (Nat.card M).factorization (primes i) := by
    calc
      Nat.card U = Nat.card (U ⧸ L) := hU_card_quot
      _ = Nat.card (S0 : Subgroup M) := hquot_card
      _ = (primes i) ^ (Nat.card M).factorization (primes i) :=
        Sylow.card_eq_multiplicity S0
  let S : Sylow (primes i) M := Sylow.ofCard U hU_card
  have hSnormal : (S : Subgroup M).Normal := by
    have hUnormal : U.Normal := by
      letI : U.Characteristic := by
        simpa [U] using hchar i.castSucc
      infer_instance
    simpa [S, U] using hUnormal
  haveI : (S : Subgroup M).Normal := hSnormal
  have hSne : (S : Subgroup M) ≠ ⊥ :=
    by simpa [S, U] using hcast_ne_bot
  let q : Nat.Primes := ⟨primes i, Fact.out⟩
  have hSnontr : Nontrivial (S : Subgroup M) :=
    (Subgroup.nontrivial_iff_ne_bot (S : Subgroup M)).2 hSne
  have hqS : q.val ∣ Nat.card (S : Subgroup M) := by
    obtain ⟨m, hmpos, hcard⟩ :=
      (S.isPGroup').nontrivial_iff_card.mp hSnontr
    rw [hcard]
    exact dvd_pow_self q.val (Nat.ne_zero_of_lt hmpos)
  have hqM : q.val ∣ Nat.card M :=
    hqS.trans (Subgroup.card_subgroup_dvd_card (S : Subgroup M))
  have hnorm_eq :
      Subgroup.normalizer (((S : Subgroup M).map M.subtype : Subgroup G) : Set G) = M :=
    section10_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot hM
      (S : Subgroup M) hSne
  refine ⟨q, ?_, hqM⟩
  refine ⟨?_, S, ?_⟩
  · simpa [subgroupPrimeSet] using hqM
  · intro x hx
    have hx' :
        x ∈ Subgroup.normalizer ((((S : Subgroup M).map M.subtype : Subgroup G)) : Set G) := by
      simpa only [section10AmbientSylowSubgroup] using hx
    rw [hnorm_eq] at hx'
    exact hx'

private theorem CFSG.section10_msigmaSubgroup_ne_bot_of_mem_sigma
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {q : Nat.Primes} (hqσ : q ∈ section10SigmaPrimes M)
    (hqM : q.val ∣ Nat.card M) :
    section10MsigmaSubgroup M ≠ ⊥ := by
  classical
  let π : Set Nat.Primes := section10SigmaPrimes M
  let K : Subgroup M := section10MsigmaSubgroup M
  have hKHall : IsHallSubgroup π K := section10_msigmaSubgroup_isHall hM
  have hq_not_index : ¬ q.val ∣ K.index := by
    intro hqidx
    exact (hKHall.p_in_pi_of_p_dvd_index q hqidx) (by simpa [π] using hqσ)
  have hcardM : Nat.card M = Nat.card K * K.index := by
    rw [K.card_mul_index]
  have hq_prod : q.val ∣ Nat.card K * K.index := by
    rw [← hcardM]
    exact hqM
  rcases q.property.dvd_or_dvd hq_prod with hqK | hqidx
  · intro hKbot
    have hcardK : Nat.card K = 1 := (Subgroup.card_eq_one (H := K)).2 hKbot
    exact q.property.not_dvd_one (by simpa [hcardK] using hqK)
  · exact False.elim (hq_not_index hqidx)

public theorem CFSG.section10_exists_pSubgroup_two_le_generatorRank_of_two_le_groupRank_pre
    {R : Type*} [Group R] [Finite R] (hrank : 2 ≤ groupRank R) :
    ∃ q : Nat.Primes, ∃ A : Subgroup R,
      IsPGroup q.val A ∧ IsMulCommutative A ∧ 2 ≤ generatorRank A := by
  let S : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R}
  have hrank' : 1 < sSup S := by
    exact lt_of_lt_of_le (by decide : 1 < 2) (by simpa [groupRank, S] using hrank)
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hqprime, hnq⟩
    exact hnq.trans (section10_primeRank_le_natCard_pre (q := q) R)
  have hSnonempty : S.Nonempty := by
    by_contra hS
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have : ¬ 1 < sSup S := by simp [hSempty]
    exact this hrank'
  have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hSnonempty hSbdd
  rcases hsSup_mem with ⟨q, hqprime, hsSup_le⟩
  have hqrank : 1 < primeRank q R := lt_of_lt_of_le hrank' hsSup_le
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
      n ≤ generatorRank A}
  have hqrank' : 1 < sSup T := by
    simpa [primeRank, T] using hqrank
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section10_generatorRank_le_natCard_pre A).trans (Subgroup.card_le_card_group A)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 1 < sSup T := by simp [hTempty]
    exact this hqrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨A, hAq, hAcomm, htSup_le⟩
  exact ⟨⟨q, hqprime⟩, A, hAq, hAcomm,
    Nat.succ_le_of_lt (lt_of_lt_of_le hqrank' htSup_le)⟩

/-- Theorem 10.2(e). -/
public theorem CFSG.theorem_10_2_e
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    section10Msigma M ≠ ⊥ := by
  classical
  by_cases hα : section10MalphaSubgroup M = ⊥
  · obtain ⟨q, hqσ, hqM⟩ :=
      section10_exists_sigma_prime_of_malpha_eq_bot hM hα
    have hKne : section10MsigmaSubgroup M ≠ ⊥ :=
      section10_msigmaSubgroup_ne_bot_of_mem_sigma hM hqσ hqM
    simpa [section10Msigma] using
      section10_map_subtype_ne_bot_of_ne_bot (M := M)
        (K := section10MsigmaSubgroup M) hKne
  · have hKne : section10MsigmaSubgroup M ≠ ⊥ := by
      intro hσbot
      exact hα <| le_bot_iff.mp <|
        (section10_malphaSubgroup_le_msigmaSubgroup hM).trans (le_of_eq hσbot)
    simpa [section10Msigma] using
      section10_map_subtype_ne_bot_of_ne_bot (M := M)
        (K := section10MsigmaSubgroup M) hKne

end Section10
