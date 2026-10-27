module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_6_c
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

/-!
# Theorem 11.7

This file contains the Section 11 Theorem 11.7 statement and proof.
-/

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section11_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (N : Subgroup M) [N.Normal] (hNne : N ≠ ⊥) :
    Subgroup.normalizer (((N : Subgroup M).map M.subtype : Subgroup G) : Set G) = M := by
  classical
  let NG : Subgroup G := (N : Subgroup M).map M.subtype
  have hNG_le_M : NG ≤ M := by
    rintro x ⟨n, _hn, rfl⟩
    exact n.2
  have hM_le_norm : M ≤ Subgroup.normalizer (NG : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases hx with ⟨n, hn, rfl⟩
      refine ⟨(⟨m, hm⟩ : M) * n * (⟨m, hm⟩ : M)⁻¹, ?_, ?_⟩
      · exact Subgroup.Normal.conj_mem inferInstance n hn ⟨m, hm⟩
      · rfl
    · intro hx
      rcases hx with ⟨n, hn, hnx⟩
      refine ⟨(⟨m, hm⟩ : M)⁻¹ * n * (⟨m, hm⟩ : M), ?_, ?_⟩
      · simpa using
          Subgroup.Normal.conj_mem inferInstance n hn ((⟨m, hm⟩ : M)⁻¹)
      · have hnx' : (n : G) = m * x * m⁻¹ := by
          simpa using hnx
        change m⁻¹ * (n : G) * m = x
        rw [hnx']
        simp [mul_assoc]
  have hnorm_proper : Subgroup.normalizer (NG : Set G) ≠ ⊤ := by
    intro htop
    have hNG_normal : NG.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have : IsSimpleGroup G := IsMinCE.simple
    rcases (haveI := hNG_normal; IsSimpleGroup.eq_bot_or_eq_top_of_normal NG) with hbot | htopNG
    · apply hNne
      ext n
      constructor
      · intro hn
        have hnG : ((n : M) : G) ∈ NG := ⟨n, hn, rfl⟩
        have hnG_bot : ((n : M) : G) ∈ (⊥ : Subgroup G) := by
          simpa [NG, hbot] using hnG
        have hn_one_G : ((n : M) : G) = 1 := by
          simpa using hnG_bot
        exact Subtype.ext (show (n : G) = 1 by simpa using hn_one_G)
      · intro hn
        rw [Subgroup.mem_bot] at hn
        simp [hn]
    · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        intro x hx
        have hxNG : x ∈ NG := by
          simp [NG, htopNG]
        exact hNG_le_M hxNG
      exact hM.ne_top (top_le_iff.mp htop_le_M)
  exact (hM.le_iff_eq hnorm_proper).mp hM_le_norm


omit [IsMinCE G] in
private theorem CFSG.section11_isPiSubgroup_singleton_of_isPGroup
    {H : Subgroup G} {q : Nat.Primes} (hH : IsPGroup q.val H) :
    IsPiSubgroup (G := G) ({q} : Set Nat.Primes) H := by
  let : Fact q.val.Prime := ⟨q.2⟩
  intro p hp
  obtain ⟨n, hncard⟩ := hH.exists_card_eq
  have hpdvdq : p.val ∣ q.val := p.2.dvd_of_dvd_pow (by simpa [hncard] using hp)
  have hpq : p = q := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 q.2).mp hpdvdq)
  simp [hpq]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_isPiSubgroup_sigma_compl_of_singleton
    {M H : Subgroup G} {q : Nat.Primes}
    (hqσ : q ∉ section10SigmaPrimes M)
    (hHq : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) H) :
    IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ H := by
  intro r hr
  have hrq : r ∈ ({q} : Set Nat.Primes) := hHq r hr
  have hr_eq_q : r = q := by simpa using hrq
  simpa [hr_eq_q] using hqσ

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_isPiSubgroup_p_compl_of_singleton
    {H : Subgroup G} {p q : Nat.Primes} (hpq : q ≠ p)
    (hHq : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) H) :
    IsPiSubgroup (G := G) (section10PPrimeSet p) H := by
  intro r hr
  have hrq : r ∈ ({q} : Set Nat.Primes) := hHq r hr
  have hr_eq_q : r = q := by simpa using hrq
  simpa [section10PPrimeSet, hr_eq_q, eq_comm] using hpq

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_mem_sigma_of_sylow_normalizer_le
    {M : Subgroup G} {q : Nat.Primes} (Q : Sylow q.val M)
    (hqM : q.val ∣ Nat.card M)
    (hQnorm : Subgroup.normalizer (section10AmbientSylowSubgroup M Q : Set G) ≤ M) :
    q ∈ section10SigmaPrimes M := by
  exact ⟨by simpa [subgroupPrimeSet] using hqM, ⟨Q, hQnorm⟩⟩

private theorem CFSG.section11_normalizer_le_maximal_of_normal_subgroup
    {M N H : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hNM : N ≤ M) [hNnorm : (N.subgroupOf M).Normal] (hNne : N ≠ ⊥)
    (hHnormN : Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup.normalizer (H : Set G) ≤ M := by
  have hNsub_ne : N.subgroupOf M ≠ ⊥ := by
    intro hbot
    apply hNne
    ext x
    constructor
    · intro hx
      have hxsub : (⟨x, hNM hx⟩ : M) ∈ N.subgroupOf M := hx
      have hxbot : (⟨x, hNM hx⟩ : M) ∈ (⊥ : Subgroup M) := by
        simpa [hbot] using hxsub
      simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)
    · intro hx
      rw [Subgroup.mem_bot] at hx
      simp [hx]
  have hNmap : (N.subgroupOf M).map M.subtype = N := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hn
    · intro hx
      exact ⟨⟨x, hNM hx⟩, hx, rfl⟩
  have hnorm_eq :
      Subgroup.normalizer (((N.subgroupOf M : Subgroup M).map M.subtype : Subgroup G) : Set G) =
        M :=
    section11_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot hM (N.subgroupOf M) hNsub_ne
  intro x hx
  have hxnorm : x ∈ Subgroup.normalizer (N : Set G) := hHnormN hx
  have hxnorm_map :
      x ∈ Subgroup.normalizer (((N.subgroupOf M : Subgroup M).map M.subtype : Subgroup G) : Set G) := by
    simpa [hNmap] using hxnorm
  rw [hnorm_eq] at hxnorm_map
  exact hxnorm_map

private theorem CFSG.section11_sigma_contradiction_of_sylow_normalizer_preserves_normal
    {M Q0 : Subgroup G} {q : Nat.Primes} (Q : Sylow q.val M)
    (hM : M ∈ section9MaximalSubgroups G) (hqσ : q ∉ section10SigmaPrimes M)
    (hqM : q.val ∣ Nat.card M) (hQ0M : Q0 ≤ M)
    [hQ0norm : (Q0.subgroupOf M).Normal] (hQ0ne : Q0 ≠ ⊥)
    (hQnormQ0 :
      Subgroup.normalizer (section10AmbientSylowSubgroup M Q : Set G) ≤
        Subgroup.normalizer (Q0 : Set G)) :
    False := by
  have hQnormM :
      Subgroup.normalizer (section10AmbientSylowSubgroup M Q : Set G) ≤ M :=
    section11_normalizer_le_maximal_of_normal_subgroup hM hQ0M hQ0ne hQnormQ0
  exact hqσ (section11_mem_sigma_of_sylow_normalizer_le Q hqM hQnormM)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_coprime_card_of_isHall_compl
    {π : Set Nat.Primes} {N E : Subgroup G}
    (hN : IsHallSubgroup π N) (hE : IsHallSubgroup πᶜ E) :
    Nat.Coprime (Nat.card N) (Nat.card E) := by
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqN hqE
  let q' : Nat.Primes := ⟨q, hqprime⟩
  exact (hE.p_in_pi_of_p_dvd_card q' hqE) (hN.p_in_pi_of_p_dvd_card q' hqN)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_coprime_index_of_isHall_compl
    {π : Set Nat.Primes} {N E : Subgroup G}
    (hN : IsHallSubgroup π N) (hE : IsHallSubgroup πᶜ E) :
    Nat.Coprime N.index E.index := by
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqN hqE
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hq_notπ : q' ∉ π := hN.p_in_pi_of_p_dvd_index q' hqN
  have hq_notπc : q' ∉ πᶜ := hE.p_in_pi_of_p_dvd_index q' hqE
  exact hq_notπ (by
    by_contra hnot
    exact hq_notπc hnot)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_card_eq_index_of_isHall_compl
    {π : Set Nat.Primes} {N E : Subgroup G}
    (hN : IsHallSubgroup π N) (hE : IsHallSubgroup πᶜ E) :
    Nat.card E = N.index := by
  have hcopEN : Nat.Coprime (Nat.card E) (Nat.card N) :=
    (section11_coprime_card_of_isHall_compl hN hE).symm
  have hE_dvd_Nidx : Nat.card E ∣ N.index := by
    have hdiv : Nat.card E ∣ Nat.card G := Subgroup.card_subgroup_dvd_card E
    have hdiv' : Nat.card E ∣ N.index * Nat.card N := by
      simpa [Subgroup.index_mul_card (H := N)] using hdiv
    exact hcopEN.dvd_of_dvd_mul_right hdiv'
  have hcopIdx : Nat.Coprime N.index E.index :=
    section11_coprime_index_of_isHall_compl hN hE
  have hNidx_dvd_E : N.index ∣ Nat.card E := by
    have hdiv : N.index ∣ Nat.card G := Subgroup.index_dvd_card (H := N)
    have hdiv' : N.index ∣ Nat.card E * E.index := by
      simpa [Subgroup.index_mul_card (H := E), mul_comm] using hdiv
    exact hcopIdx.dvd_of_dvd_mul_right hdiv'
  exact Nat.dvd_antisymm hE_dvd_Nidx hNidx_dvd_E

omit [IsMinCE G] in
public theorem CFSG.section11_isComplement_of_isHall_compl
    {π : Set Nat.Primes} {N E : Subgroup G}
    (hN : IsHallSubgroup π N) (hE : IsHallSubgroup πᶜ E) :
    N.IsComplement' E := by
  have hcardE : Nat.card E = N.index :=
    section11_card_eq_index_of_isHall_compl hN hE
  have hcard_mul : Nat.card N * Nat.card E = Nat.card G := by
    rw [hcardE, mul_comm]
    exact Subgroup.index_mul_card (H := N)
  exact Subgroup.isComplement'_of_coprime hcard_mul
    (section11_coprime_card_of_isHall_compl hN hE)


private theorem CFSG.section11_exists_msigma_complement_containing_P
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    ∃ E : Subgroup M,
      (section10MsigmaSubgroup M).IsComplement' E ∧ (P : Subgroup M) ≤ E := by
  classical
  let : MulDistribMulAction Unit M := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hPinv : IsInvariant Unit M (P : Subgroup M) := by
    refine ⟨?_⟩
    intro _ x
    simp
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr h11.maximal.1)
  have hcop : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
  have hPsingle : IsPiSubgroup (G := M) ({p} : Set Nat.Primes) (P : Subgroup M) :=
    section11_isPiSubgroup_singleton_of_isPGroup (G := M) P.isPGroup'
  have hPσc : IsPiSubgroup (G := M) (section10SigmaPrimes M)ᶜ (P : Subgroup M) := by
    intro q hqP
    have hqp : q ∈ ({p} : Set Nat.Primes) := hPsingle q hqP
    have hq_eq : q = p := by simpa using hqp
    simpa [hq_eq] using h11.not_sigma
  obtain ⟨E, hEhall, _hEinv, hPleE⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := Unit) hsolvM hcop (section10SigmaPrimes M)ᶜ
      (P : Subgroup M) hPσc hPinv
  have hNhall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
    (theorem_10_2_b h11.maximal).2
  exact ⟨E, section11_isComplement_of_isHall_compl hNhall hEhall, hPleE⟩

private theorem CFSG.section11_msigma_complement_isHall_sigma_compl
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {E : Subgroup M}
    (hcomp : (section10MsigmaSubgroup M).IsComplement' E) :
    IsHallSubgroup (section10SigmaPrimes M)ᶜ E := by
  classical
  have hNhall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
    (theorem_10_2_b hM).2
  refine isHallSubgroup_of (G := M) (section10SigmaPrimes M)ᶜ E ?_ ?_
  · intro q hqE hqσ
    have hqNidx : q.val ∣ (section10MsigmaSubgroup M).index := by
      simpa [hcomp.symm.index_eq_card] using hqE
    exact (hNhall.p_in_pi_of_p_dvd_index q hqNidx) hqσ
  · intro q hq_not_σc hqEidx
    have hqN : q.val ∣ Nat.card (section10MsigmaSubgroup M) := by
      simpa [hcomp.index_eq_card] using hqEidx
    have hqσ : q ∈ section10SigmaPrimes M :=
      hNhall.p_in_pi_of_p_dvd_card q hqN
    exact hq_not_σc hqσ

private theorem CFSG.section11_prime_not_sigma_of_dvd_msigma_complement
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {E : Subgroup M}
    (hcomp : (section10MsigmaSubgroup M).IsComplement' E) {q : Nat.Primes}
    (hqE : q.val ∣ Nat.card E) :
    q ∉ section10SigmaPrimes M := by
  exact (section11_msigma_complement_isHall_sigma_compl hM hcomp).p_in_pi_of_p_dvd_card q hqE

omit [IsMinCE G] in
private theorem CFSG.section11_A_subgroupOf_le_sylow
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    A.subgroupOf M ≤ (P : Subgroup M) := by
  intro a ha
  have hamb : ((a : M) : G) ∈ section10AmbientSylowSubgroup M P :=
    h11.A_le_ambient_sylow ha
  rcases Subgroup.mem_map.mp hamb with ⟨y, hyP, hy_eq⟩
  have hya : y = a := Subtype.ext hy_eq
  simpa [hya] using hyP

omit [IsMinCE G] in
private theorem CFSG.section11_A_subgroupOf_ne_bot
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    A.subgroupOf M ≠ ⊥ := by
  intro hbot
  exact h11.A_ne_bot (by
    ext x
    constructor
    · intro hx
      have hxsub : (⟨x, h11.A_le_M hx⟩ : M) ∈ A.subgroupOf M := hx
      have hxbot : (⟨x, h11.A_le_M hx⟩ : M) ∈ (⊥ : Subgroup M) := by
        simpa [hbot] using hxsub
      simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)
    · intro hx
      rw [Subgroup.mem_bot] at hx
      simp [hx])

omit [IsMinCE G] in
private theorem CFSG.section11_prime_dvd_complement_of_contains_P
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E) :
    p.val ∣ Nat.card E := by
  have : Fact p.val.Prime := ⟨p.property⟩
  have hpP : p.val ∣ Nat.card (P : Subgroup M) := by
    rcases P.isPGroup'.card_eq_or_dvd with hcard | hpdiv
    · exfalso
      have hPbot : (P : Subgroup M) = ⊥ :=
        (Subgroup.card_eq_one (H := (P : Subgroup M))).1 hcard
      have hAsub_bot : A.subgroupOf M = ⊥ := by
        apply le_bot_iff.mp
        intro x hx
        have hxP : x ∈ (P : Subgroup M) := section11_A_subgroupOf_le_sylow h11 hx
        simpa [hPbot] using hxP
      exact section11_A_subgroupOf_ne_bot h11 hAsub_bot
    · exact hpdiv
  exact hpP.trans (Subgroup.card_dvd_of_le hPleE)

omit [IsMinCE G] in
private theorem CFSG.section11_normalIn_msigma_sup_of_complement_A_normal
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hcomp : (section10MsigmaSubgroup M).IsComplement' E)
    (hAleE : A.subgroupOf M ≤ E)
    [hAnormE : ((A.subgroupOf M).subgroupOf E).Normal] :
    section10NormalIn (section10Msigma M ⊔ A) M := by
  classical
  let N : Subgroup M := section10MsigmaSubgroup M
  let B : Subgroup M := A.subgroupOf M
  let S : Subgroup M := N ⊔ B
  have hB_norm_E : E ≤ Subgroup.normalizer (B : Set M) := by
    simpa [B] using Subgroup.le_normalizer_of_normal_subgroupOf hAleE
  have hE_norm_N : E ≤ Subgroup.normalizer (N : Set M) := by
    simpa [N] using (Subgroup.le_normalizer_of_normal (H := section10MsigmaSubgroup M))
  have hN_norm_S : N ≤ Subgroup.normalizer (S : Set M) :=
    le_sup_left.trans (Subgroup.le_normalizer (H := S))
  have hE_norm_S : E ≤ Subgroup.normalizer (S : Set M) := by
    refine subgroup_le_normalizer_of_conj_mem S E ?_
    intro e x hxS
    rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := N) (t := B)).1 hxS with
      ⟨n, hnN, b, hbB, hnb⟩
    have henN : (e : M) * n * (e : M)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hE_norm_N e.property) n).1 hnN
    have hebB : (e : M) * b * (e : M)⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hB_norm_E e.property) b).1 hbB
    change (e : M) * x * (e : M)⁻¹ ∈ S
    rw [← hnb]
    have hmul :
        (e : M) * (n * b) * (e : M)⁻¹ =
          ((e : M) * n * (e : M)⁻¹) * ((e : M) * b * (e : M)⁻¹) := by
      group
    rw [hmul]
    exact S.mul_mem ((show N ≤ S from le_sup_left) henN) ((show B ≤ S from le_sup_right) hebB)
  have htop_norm : (⊤ : Subgroup M) ≤ Subgroup.normalizer (S : Set M) := by
    rw [← hcomp.sup_eq_top]
    exact sup_le hN_norm_S hE_norm_S
  have hS_normal : S.Normal := by
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop_norm)
  have hsup_le_M : section10Msigma M ⊔ A ≤ M :=
    sup_le (section11_msigma_le M) h11.A_le_M
  refine ⟨hsup_le_M, ?_⟩
  have hsub_eq : (section10Msigma M ⊔ A).subgroupOf M = S := by
    have hMsig_le_M : section10Msigma M ≤ M := section11_msigma_le M
    have hMsig_sub_eq :
        (section10Msigma M).subgroupOf M = section10MsigmaSubgroup M := by
      change ((section10MsigmaSubgroup M).map M.subtype).comap M.subtype =
        section10MsigmaSubgroup M
      exact
        Subgroup.comap_map_eq_self_of_injective
          (H := section10MsigmaSubgroup M) (f := M.subtype) M.subtype_injective
    calc
      (section10Msigma M ⊔ A).subgroupOf M =
          (section10Msigma M).subgroupOf M ⊔ A.subgroupOf M := by
        exact
          Subgroup.subgroupOf_sup (A := section10Msigma M) (A' := A) (B := M)
            hMsig_le_M h11.A_le_M
      _ = S := by
        simp [S, N, B, hMsig_sub_eq]
  simpa [hsub_eq] using hS_normal

private theorem CFSG.section11_complement_groupRank_le_two
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hcomp : (section10MsigmaSubgroup M).IsComplement' E) :
    groupRank E ≤ 2 := by
  exact section10_hall_compl_sigma_groupRank_le_two h11.maximal
    (section11_msigma_complement_isHall_sigma_compl h11.maximal hcomp)


private theorem CFSG.section11_complement_characteristic_hall_ge_gt
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hcomp : (section10MsigmaSubgroup M).IsComplement' E)
    (hPleE : (P : Subgroup M) ≤ E) :
    ∃ L K : Subgroup E,
      L.Characteristic ∧ K.Characteristic ∧
        IsHallSubgroup ({q : Nat.Primes | p.val ≤ q.val}) L ∧
          IsHallSubgroup ({q : Nat.Primes | p.val < q.val}) K ∧ K ≤ L := by
  classical
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr h11.maximal.1)
  have hsolvE : Group.IsSolvable E := by
    let : Group.IsSolvable M := hsolvM
    infer_instance
  have hE_dvd_G : Nat.card E ∣ Nat.card G :=
    (Subgroup.card_subgroup_dvd_card E).trans (Subgroup.card_subgroup_dvd_card M)
  have hoddE : Odd (Nat.card E) := IsMinCE.odd_order.of_dvd_nat hE_dvd_G
  have hpE : p.val ∣ Nat.card E :=
    section11_prime_dvd_complement_of_contains_P h11 hPleE
  exact theorem_4_20_c_characteristic_hall_ge_gt
    (G := E) hsolvE hoddE
    (Or.inl (section11_complement_groupRank_le_two h11 hcomp)) hpE

private theorem CFSG.section11_complement_piCore_gt_isHall
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hcomp : (section10MsigmaSubgroup M).IsComplement' E)
    (hPleE : (P : Subgroup M) ≤ E) :
    IsHallSubgroup ({q : Nat.Primes | p.val < q.val})
      (piCore ({q : Nat.Primes | p.val < q.val}) E) := by
  classical
  let π : Set Nat.Primes := {q : Nat.Primes | p.val < q.val}
  obtain ⟨_L, K, _hLchar, hKchar, _hLhall, hKhall, _hKleL⟩ :=
    section11_complement_characteristic_hall_ge_gt h11 hcomp hPleE
  have hKnorm : K.Normal := by
    let : K.Characteristic := hKchar
    infer_instance
  let : K.Normal := hKnorm
  have hKπ : IsPiSubgroup (G := E) π K := hKhall.p_in_pi_of_p_dvd_card
  have hK_le_core : K ≤ piCore π E :=
    le_piCore_of_normal_isPiSubgroup (G := E) π K hKπ
  have hcore_le_K : piCore π E ≤ K := by
    have hcoreπ : IsPiSubgroup (G := E) π (piCore π E) := piCore_isPiSubgroup (G := E) π
    have hcore_norm_K : piCore π E ≤ Subgroup.normalizer (K : Set E) := by
      simp [Subgroup.normalizer_eq_top]
    exact section11_hall_le_of_isPiSubgroup_of_le_normalizer
      (G := E) hKhall hcoreπ hcore_norm_K
  have hcore_eq : piCore π E = K := le_antisymm hcore_le_K hK_le_core
  change IsHallSubgroup π (piCore π E)
  rw [hcore_eq]
  simpa [π] using hKhall

omit [IsMinCE G] in
private theorem CFSG.section11_complement_sylow_le_hall_ge
    {M : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    {E : Subgroup M} (hPleE : (P : Subgroup M) ≤ E)
    {L : Subgroup E} (hLchar : L.Characteristic)
    (hLhall : IsHallSubgroup ({q : Nat.Primes | p.val ≤ q.val}) L) :
    (P.subtype hPleE : Subgroup E) ≤ L := by
  have : Fact p.val.Prime := ⟨p.property⟩
  have hPπ_single :
      IsPiSubgroup (G := E) ({p} : Set Nat.Primes) (P.subtype hPleE : Subgroup E) :=
    section11_isPiSubgroup_singleton_of_isPGroup (G := E) (P.subtype hPleE).isPGroup'
  have hPπ :
      IsPiSubgroup (G := E) ({q : Nat.Primes | p.val ≤ q.val})
        (P.subtype hPleE : Subgroup E) := by
    intro q hq
    have hqp : q ∈ ({p} : Set Nat.Primes) := hPπ_single q hq
    have hq_eq : q = p := by simpa using hqp
    simp [hq_eq]
  have hP_norm_L :
      (P.subtype hPleE : Subgroup E) ≤ Subgroup.normalizer (L : Set E) := by
    let : L.Characteristic := hLchar
    have : L.Normal := by infer_instance
    simp [Subgroup.normalizer_eq_top]
  exact section11_hall_le_of_isPiSubgroup_of_le_normalizer
    (G := E) hLhall hPπ hP_norm_L

omit [IsMinCE G] in
private theorem CFSG.section11_complement_A_le_hall_ge
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E)
    {L : Subgroup E} (hLchar : L.Characteristic)
    (hLhall : IsHallSubgroup ({q : Nat.Primes | p.val ≤ q.val}) L) :
    (A.subgroupOf M).subgroupOf E ≤ L := by
  have hA_le_Psub : (A.subgroupOf M).subgroupOf E ≤ (P.subtype hPleE : Subgroup E) := by
    intro x hx
    change (x : M) ∈ (P : Subgroup M)
    exact section11_A_subgroupOf_le_sylow h11 hx
  exact hA_le_Psub.trans
    (section11_complement_sylow_le_hall_ge
      (M := M) (p := p) (P := P) hPleE hLchar hLhall)

omit [IsMinCE G] in
private theorem CFSG.section11_complement_piCore_gt_le_hall_ge
    {M : Subgroup G} {p : Nat.Primes} {E : Subgroup M} {L : Subgroup E}
    (hLchar : L.Characteristic)
    (hLhall : IsHallSubgroup ({q : Nat.Primes | p.val ≤ q.val}) L) :
    piCore ({q : Nat.Primes | p.val < q.val}) E ≤ L := by
  classical
  let πgt : Set Nat.Primes := {q : Nat.Primes | p.val < q.val}
  let πge : Set Nat.Primes := {q : Nat.Primes | p.val ≤ q.val}
  have hcoreπgt : IsPiSubgroup (G := E) πgt (piCore πgt E) :=
    piCore_isPiSubgroup (G := E) πgt
  have hcoreπge : IsPiSubgroup (G := E) πge (piCore πgt E) := by
    intro q hq
    have hqgt : p.val < q.val := by
      simpa [πgt] using hcoreπgt q hq
    exact hqgt.le
  have hcore_norm_L : piCore πgt E ≤ Subgroup.normalizer (L : Set E) := by
    let : L.Characteristic := hLchar
    have : L.Normal := by infer_instance
    simp [Subgroup.normalizer_eq_top]
  exact section11_hall_le_of_isPiSubgroup_of_le_normalizer
    (G := E) (π := πge) hLhall hcoreπge hcore_norm_L

private theorem CFSG.section11_complement_exists_normal_hall_ge_containing_tail_and_sylow
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hcomp : (section10MsigmaSubgroup M).IsComplement' E)
    (hPleE : (P : Subgroup M) ≤ E) :
    ∃ L : Subgroup E,
      L.Characteristic ∧ L.Normal ∧
        IsHallSubgroup ({q : Nat.Primes | p.val ≤ q.val}) L ∧
          piCore ({q : Nat.Primes | p.val < q.val}) E ≤ L ∧
            (P.subtype hPleE : Subgroup E) ≤ L ∧
              (A.subgroupOf M).subgroupOf E ≤ L := by
  classical
  obtain ⟨L, _K, hLchar, _hKchar, hLhall, _hKhall, _hKleL⟩ :=
    section11_complement_characteristic_hall_ge_gt h11 hcomp hPleE
  have hLnorm : L.Normal := by
    let : L.Characteristic := hLchar
    infer_instance
  refine ⟨L, hLchar, hLnorm, hLhall, ?_, ?_, ?_⟩
  · exact section11_complement_piCore_gt_le_hall_ge
      (M := M) (p := p) (E := E) (L := L) hLchar hLhall
  · exact section11_complement_sylow_le_hall_ge
      (M := M) (p := p) (P := P)
      hPleE hLchar hLhall
  · exact section11_complement_A_le_hall_ge h11 hPleE hLchar hLhall

private theorem CFSG.section11_complement_piCore_gt_subgroupOf_hall_ge_isHall
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hcomp : (section10MsigmaSubgroup M).IsComplement' E)
    (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hKleL : piCore ({q : Nat.Primes | p.val < q.val}) E ≤ L) :
    IsHallSubgroup ({q : Nat.Primes | p.val < q.val})
      ((piCore ({q : Nat.Primes | p.val < q.val}) E).subgroupOf L) := by
  exact (section11_complement_piCore_gt_isHall h11 hcomp hPleE).subgroupOf hKleL


omit [IsMinCE G] in
private theorem CFSG.section11_complement_sylow_subgroupOf_hall_ge_isHall_singleton
    {M : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    {E : Subgroup M} (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hPLeL : (P.subtype hPleE : Subgroup E) ≤ L) :
    IsHallSubgroup ({p} : Set Nat.Primes)
      ((P.subtype hPleE : Subgroup E).subgroupOf L) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let PE : Sylow p.val E := P.subtype hPleE
  have hPsub_p : IsPGroup p.val ((PE : Subgroup E).subgroupOf L) := by
    exact PE.isPGroup'.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := (PE : Subgroup E)) (K := L) hPLeL).symm
  have hPsubπ :
      IsPiSubgroup (G := L) ({p} : Set Nat.Primes) ((PE : Subgroup E).subgroupOf L) :=
    section11_isPiSubgroup_singleton_of_isPGroup (G := L) hPsub_p
  refine isHallSubgroup_of (G := L) ({p} : Set Nat.Primes)
    ((PE : Subgroup E).subgroupOf L) ?_ ?_
  · intro q hq
    exact hPsubπ q hq
  · intro q hq_mem hq_idx
    have hidx_dvd : ((PE : Subgroup E).subgroupOf L).index ∣ (PE : Subgroup E).index := by
      have hmap : (((PE : Subgroup E).subgroupOf L).map L.subtype : Subgroup E) =
          (PE : Subgroup E) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hPLeL hx⟩, hx, rfl⟩
      have hidx_map :
          (((PE : Subgroup E).subgroupOf L).map L.subtype : Subgroup E).index =
            ((PE : Subgroup E).subgroupOf L).index * L.index :=
        Subgroup.index_map_subtype (K := ((PE : Subgroup E).subgroupOf L))
      exact ⟨L.index, by simpa [hmap] using hidx_map⟩
    have hq_eq_p : q = p := by simpa using hq_mem
    exact PE.not_dvd_index (by
      simpa [hq_eq_p] using hq_idx.trans hidx_dvd)

private theorem CFSG.section11_complement_piCore_gt_subgroupOf_hall_ge_isHall_p_compl
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hcomp : (section10MsigmaSubgroup M).IsComplement' E)
    (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hLhall : IsHallSubgroup ({q : Nat.Primes | p.val ≤ q.val}) L)
    (hKleL : piCore ({q : Nat.Primes | p.val < q.val}) E ≤ L) :
    IsHallSubgroup ({p}ᶜ : Set Nat.Primes)
      ((piCore ({q : Nat.Primes | p.val < q.val}) E).subgroupOf L) := by
  classical
  let πgt : Set Nat.Primes := {q : Nat.Primes | p.val < q.val}
  let K : Subgroup E := piCore πgt E
  have hKhall_gt : IsHallSubgroup πgt (K.subgroupOf L) := by
    simpa [K, πgt] using
      section11_complement_piCore_gt_subgroupOf_hall_ge_isHall
        h11 hcomp hPleE (L := L) hKleL
  refine isHallSubgroup_of (G := L) ({p}ᶜ : Set Nat.Primes) (K.subgroupOf L) ?_ ?_
  · intro q hq
    have hqgt : p.val < q.val := hKhall_gt.p_in_pi_of_p_dvd_card q hq
    intro hqmem
    have hq_eq_p : q = p := by simpa using hqmem
    have hp_lt_p : p.val < p.val := by
      rw [hq_eq_p] at hqgt
      exact hqgt
    exact (Nat.lt_irrefl p.val) hp_lt_p
  · intro q hq_not_p hq_idx
    have hqL : q.val ∣ Nat.card L :=
      hq_idx.trans (Subgroup.index_dvd_card (H := K.subgroupOf L))
    have hqge : p.val ≤ q.val := hLhall.p_in_pi_of_p_dvd_card q hqL
    have hp_ne_q : p.val ≠ q.val := by
      intro hpq
      have hq_eq_p : q = p := Subtype.ext hpq.symm
      exact hq_not_p hq_eq_p
    have hqgt : p.val < q.val := lt_of_le_of_ne hqge hp_ne_q
    exact (hKhall_gt.p_in_pi_of_p_dvd_index q hq_idx) hqgt

private theorem CFSG.section11_complement_tail_sylow_isComplement_in_hall_ge
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hcomp : (section10MsigmaSubgroup M).IsComplement' E)
    (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hLhall : IsHallSubgroup ({q : Nat.Primes | p.val ≤ q.val}) L)
    (hKleL : piCore ({q : Nat.Primes | p.val < q.val}) E ≤ L)
    (hPLeL : (P.subtype hPleE : Subgroup E) ≤ L) :
    ((piCore ({q : Nat.Primes | p.val < q.val}) E).subgroupOf L).IsComplement'
      ((P.subtype hPleE : Subgroup E).subgroupOf L) := by
  have hKHall :
      IsHallSubgroup ({p}ᶜ : Set Nat.Primes)
        ((piCore ({q : Nat.Primes | p.val < q.val}) E).subgroupOf L) :=
    section11_complement_piCore_gt_subgroupOf_hall_ge_isHall_p_compl
      h11 hcomp hPleE hLhall hKleL
  have hPHall :
      IsHallSubgroup (({p}ᶜ : Set Nat.Primes)ᶜ)
        ((P.subtype hPleE : Subgroup E).subgroupOf L) := by
    simpa using
      section11_complement_sylow_subgroupOf_hall_ge_isHall_singleton
        (G := G) hPleE hPLeL
  exact section11_isComplement_of_isHall_compl hKHall hPHall

private theorem CFSG.section11_theorem_11_7_complement_setup
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P)
    (hnot : ¬ section10NormalIn (section10Msigma M ⊔ A) M) :
    ∃ E : Subgroup M, ∃ _hcomp : (section10MsigmaSubgroup M).IsComplement' E,
      ∃ hPleE : (P : Subgroup M) ≤ E, ∃ L : Subgroup E,
        L.Characteristic ∧ L.Normal ∧
          IsHallSubgroup ({q : Nat.Primes | p.val ≤ q.val}) L ∧
            piCore ({q : Nat.Primes | p.val < q.val}) E ≤ L ∧
              (P.subtype hPleE : Subgroup E) ≤ L ∧
                (A.subgroupOf M).subgroupOf E ≤ L ∧
                  ¬ ((A.subgroupOf M).subgroupOf E).Normal ∧
                    ((piCore ({q : Nat.Primes | p.val < q.val}) E).subgroupOf L).IsComplement'
                      ((P.subtype hPleE : Subgroup E).subgroupOf L) := by
  classical
  obtain ⟨E, hcomp, hPleE⟩ := section11_exists_msigma_complement_containing_P h11
  obtain ⟨L, hLchar, hLnorm, hLhall, hKleL, hPLeL, hALeL⟩ :=
    section11_complement_exists_normal_hall_ge_containing_tail_and_sylow h11 hcomp hPleE
  have hAleE : A.subgroupOf M ≤ E := by
    intro x hx
    exact hPleE (section11_A_subgroupOf_le_sylow h11 hx)
  have hAnotE : ¬ ((A.subgroupOf M).subgroupOf E).Normal := by
    intro hAnorm
    let : ((A.subgroupOf M).subgroupOf E).Normal := hAnorm
    exact hnot (section11_normalIn_msigma_sup_of_complement_A_normal h11 hcomp hAleE)
  have hKPcomp :
      ((piCore ({q : Nat.Primes | p.val < q.val}) E).subgroupOf L).IsComplement'
        ((P.subtype hPleE : Subgroup E).subgroupOf L) :=
    section11_complement_tail_sylow_isComplement_in_hall_ge h11 hcomp hPleE hLhall hKleL hPLeL
  exact ⟨E, hcomp, hPleE, L, hLchar, hLnorm, hLhall, hKleL, hPLeL, hALeL,
    hAnotE, hKPcomp⟩

omit [Finite G] [IsMinCE G] in
set_option backward.isDefEq.respectTransparency false in
private theorem CFSG.section11_characteristic_map_subtype_of_characteristic
    {H : Subgroup G} [hH : H.Characteristic] {K : Subgroup H}
    [hK : K.Characteristic] :
    (K.map H.subtype : Subgroup G).Characteristic := by
  classical
  rw [Subgroup.characteristic_iff_map_le]
  intro φ x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  rcases Subgroup.mem_map.mp hy with ⟨k, hk, rfl⟩
  have hHmap : H.map φ.toMonoidHom = H :=
    Subgroup.characteristic_iff_map_eq.mp hH φ
  let φH : H ≃* H := (φ.subgroupMap H).trans (MulEquiv.subgroupCongr hHmap)
  have hk_image : φH k ∈ K := by
    have hKmap : K.map φH.toMonoidHom = K :=
      Subgroup.characteristic_iff_map_eq.mp hK φH
    have : φH k ∈ K.map φH.toMonoidHom := ⟨k, hk, rfl⟩
    rw [hKmap] at this
    exact this
  refine ⟨φH k, hk_image, ?_⟩
  simp [φH]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_mem_omegaOne_pow_eq_one_of_isMulCommutative
    {H : Type*} [Group H] [IsMulCommutative H] {p : ℕ} {x : H}
    (hx : x ∈ omega₁ (G := H) (p := p)) :
    x ^ p = 1 := by
  rw [omega₁, omega] at hx
  exact
    Subgroup.closure_induction (k := {y : H | y ^ (p ^ 1) = 1})
      (p := fun y _hy => y ^ p = 1) (x := x)
      (by
        intro y hy
        simpa [pow_one] using hy)
      (by simp)
      (by
        intro y z _hy _hz hypow hzpow
        have hyz : Commute y z :=
          (IsMulCommutative.is_comm (M := H)).comm y z
        calc
          (y * z) ^ p = y ^ p * z ^ p := hyz.mul_pow p
          _ = 1 := by simp [hypow, hzpow])
      (by
        intro y _hy hypow
        simpa [inv_pow] using congrArg Inv.inv hypow)
      hx

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_pCore_le_sylow
    {H : Type*} [Group H] {p : ℕ} [Fact p.Prime] (S : Sylow p H) :
    pCore p H ≤ (S : Subgroup H) := by
  have hsup_p : IsPGroup p (((S : Subgroup H) ⊔ pCore p H : Subgroup H)) := by
    exact IsPGroup.to_sup_of_normal_right (p := p) (H := (S : Subgroup H))
      (K := pCore p H) S.isPGroup' (pCore_isPGroup (G := H) (p := p))
  have hEq : (((S : Subgroup H) ⊔ pCore p H : Subgroup H)) = (S : Subgroup H) :=
    S.3 hsup_p le_sup_left
  exact sup_eq_left.mp hEq

omit [IsMinCE G] in
private theorem CFSG.section11_complement_pCore_hall_ge_le_sylow
    {M : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    {E : Subgroup M} (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hPLeL : (P.subtype hPleE : Subgroup E) ≤ L) :
    pCore p.val L ≤ ((P.subtype hPleE : Subgroup E).subgroupOf L) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let PL : Subgroup L := (P.subtype hPleE : Subgroup E).subgroupOf L
  have hPHall :
      IsHallSubgroup ({p} : Set Nat.Primes)
        PL :=
    section11_complement_sylow_subgroupOf_hall_ge_isHall_singleton
      (G := G) hPleE hPLeL
  let ι : PL →* (P.subtype hPleE : Subgroup E) := {
    toFun x := ⟨(((x : PL) : L) : E), x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hPLp : IsPGroup p.val PL := by
    exact (P.subtype hPleE).isPGroup'.of_injective ι (by
      intro x y hxy
      have hE :
          (((x : PL) : L) : E) = (((y : PL) : L) : E) :=
        congrArg (fun z : (P.subtype hPleE : Subgroup E) => (z : E)) hxy
      apply Subtype.ext
      apply Subtype.ext
      exact hE)
  have hp_not_dvd_index : ¬ p.val ∣ PL.index := by
    intro hp_dvd
    exact (hPHall.p_in_pi_of_p_dvd_index p hp_dvd) (by simp)
  let S : Sylow p.val L := IsPGroup.toSylow (p := p.val) hPLp hp_not_dvd_index
  simpa [S, PL, IsPGroup.toSylow_coe] using section11_pCore_le_sylow S

private theorem CFSG.section11_complement_sylow_subgroupOf_hall_ge_isMulCommutative
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (_hPLeL : (P.subtype hPleE : Subgroup E) ≤ L) :
    IsMulCommutative ((P.subtype hPleE : Subgroup E).subgroupOf L) := by
  classical
  have hPcomm : IsMulCommutative (P : Subgroup M) := theorem_11_5 h11 P
  refine ⟨⟨?_⟩⟩
  intro x y
  apply Subtype.ext
  change (((x : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) *
      ((y : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) =
    ((y : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) *
      ((x : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L))
  apply Subtype.ext
  change ((((x : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) : E) *
      (((y : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) : E) =
    (((y : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) : E) *
      (((x : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) : E))
  apply Subtype.ext
  change ((((x : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) : E) : M) *
      ((((y : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) : E) : M) =
    ((((y : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) : E) : M) *
      ((((x : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) : E) : M)
  let xp : (P : Subgroup M) :=
    ⟨((((x : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) : E) : M), by
      change (((x : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) : E) ∈
        (P.subtype hPleE : Subgroup E)
      exact x.property⟩
  let yp : (P : Subgroup M) :=
    ⟨((((y : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) : E) : M), by
      change (((y : ((P.subtype hPleE : Subgroup E).subgroupOf L)) : L) : E) ∈
        (P.subtype hPleE : Subgroup E)
      exact y.property⟩
  simpa [xp, yp] using hPcomm.is_comm.comm xp yp

private theorem CFSG.section11_complement_pCore_hall_ge_isMulCommutative
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hPLeL : (P.subtype hPleE : Subgroup E) ≤ L) :
    IsMulCommutative (pCore p.val L) := by
  classical
  let PL : Subgroup L := (P.subtype hPleE : Subgroup E).subgroupOf L
  have hcore_le_PL : pCore p.val L ≤ PL :=
    section11_complement_pCore_hall_ge_le_sylow (G := G) hPleE hPLeL
  have : IsMulCommutative PL :=
    section11_complement_sylow_subgroupOf_hall_ge_isMulCommutative h11 hPleE hPLeL
  refine ⟨⟨?_⟩⟩
  intro x y
  apply Subtype.ext
  let xPL : PL := ⟨(x : L), hcore_le_PL x.property⟩
  let yPL : PL := ⟨(y : L), hcore_le_PL y.property⟩
  simpa [xPL, yPL] using congrArg Subtype.val
    ((IsMulCommutative.is_comm (M := PL)).comm xPL yPL)

private theorem CFSG.section11_complement_A_normal_in_hall_ge_of_centralizes_tail
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hKPcomp :
      ((piCore ({q : Nat.Primes | p.val < q.val}) E).subgroupOf L).IsComplement'
        ((P.subtype hPleE : Subgroup E).subgroupOf L))
    (hAcent :
      (A.subgroupOf M).subgroupOf E ≤
        Subgroup.centralizer (piCore ({q : Nat.Primes | p.val < q.val}) E : Set E)) :
    (((A.subgroupOf M).subgroupOf E).subgroupOf L).Normal := by
  classical
  let K : Subgroup E := piCore ({q : Nat.Primes | p.val < q.val}) E
  let PE : Subgroup E := P.subtype hPleE
  let AE : Subgroup E := (A.subgroupOf M).subgroupOf E
  let AL : Subgroup L := AE.subgroupOf L
  have hPcomm : IsMulCommutative (P : Subgroup M) := theorem_11_5 h11 P
  have hA_le_P : A.subgroupOf M ≤ (P : Subgroup M) :=
    section11_A_subgroupOf_le_sylow h11
  refine ⟨?_⟩
  intro a ha l
  change l * a * l⁻¹ ∈ AL
  rcases (hKPcomp.existsUnique l).exists with ⟨⟨k, r⟩, hkr⟩
  have haAE : (a : E) ∈ AE := ha
  have hrP : ((r : L) : E) ∈ PE := r.2
  have hkK : ((k : L) : E) ∈ K := k.2
  have hr_norm_a : ((r : L) : E) * (a : E) * ((r : L) : E)⁻¹ = (a : E) := by
    apply Subtype.ext
    change (((r : L) : E) : M) * ((a : L) : E) * (((r : L) : E) : M)⁻¹ =
      (((a : L) : E) : M)
    have hrP_M : (((r : L) : E) : M) ∈ (P : Subgroup M) := by
      change (((r : L) : E) : M) ∈ (P : Subgroup M) at hrP
      exact hrP
    have haP_M : (((a : L) : E) : M) ∈ (P : Subgroup M) := by
      exact hA_le_P haAE
    let rp : (P : Subgroup M) := ⟨(((r : L) : E) : M), hrP_M⟩
    let ap : (P : Subgroup M) := ⟨(((a : L) : E) : M), haP_M⟩
    have hcomm : (((r : L) : E) : M) * (((a : L) : E) : M) =
        (((a : L) : E) : M) * (((r : L) : E) : M) := by
      simpa [rp, ap] using hPcomm.is_comm.comm rp ap
    rw [hcomm]
    simp [mul_assoc]
  have hk_norm_a : ((k : L) : E) * (a : E) * ((k : L) : E)⁻¹ = (a : E) := by
    have hacent : (a : E) ∈ Subgroup.centralizer (K : Set E) := hAcent haAE
    have hcomm : ((k : L) : E) * (a : E) = (a : E) * ((k : L) : E) := by
      exact Subgroup.mem_centralizer_iff.mp hacent ((k : L) : E) hkK
    rw [hcomm]
    simp [mul_assoc]
  have hconj_eq : (l : E) * (a : E) * (l : E)⁻¹ = (a : E) := by
    have hl_eq : (l : E) = ((k : L) : E) * ((r : L) : E) := by
      simpa using congrArg (fun x : L => (x : E)) hkr.symm
    rw [hl_eq]
    calc
      (((k : L) : E) * ((r : L) : E)) * (a : E) *
          (((k : L) : E) * ((r : L) : E))⁻¹ =
          ((k : L) : E) * (((r : L) : E) * (a : E) * ((r : L) : E)⁻¹) *
            ((k : L) : E)⁻¹ := by
            group
      _ = ((k : L) : E) * (a : E) * ((k : L) : E)⁻¹ := by rw [hr_norm_a]
      _ = (a : E) := hk_norm_a
  have hmemAE : (l : E) * (a : E) * (l : E)⁻¹ ∈ AE := by
    simpa [hconj_eq] using haAE
  exact hmemAE

private theorem CFSG.section11_complement_A_subgroupOf_hall_ge_le_pCore_of_centralizes_tail
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hKPcomp :
      ((piCore ({q : Nat.Primes | p.val < q.val}) E).subgroupOf L).IsComplement'
        ((P.subtype hPleE : Subgroup E).subgroupOf L))
    (hAcent :
      (A.subgroupOf M).subgroupOf E ≤
        Subgroup.centralizer (piCore ({q : Nat.Primes | p.val < q.val}) E : Set E)) :
    (((A.subgroupOf M).subgroupOf E).subgroupOf L) ≤ pCore p.val L := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let AE : Subgroup E := (A.subgroupOf M).subgroupOf E
  let AL : Subgroup L := AE.subgroupOf L
  have : AL.Normal :=
    section11_complement_A_normal_in_hall_ge_of_centralizes_tail
      (G := G) h11 hPleE hKPcomp hAcent
  have hAp : IsPGroup p.val A := by
    rcases h11.A_rank_two with ⟨_hAcard, hAelem⟩
    let : IsElementaryAbelian p.val A := hAelem
    exact IsElementaryAbelian.isPGroup p.val A
  let ι : AL →* A := {
    toFun x := ⟨(((((x : AL) : L) : E) : M) : G), by
      change ((((x : AL) : L) : E) : M) ∈ A.subgroupOf M
      change (((x : AL) : L) : E) ∈ AE
      exact x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hALp : IsPGroup p.val AL := by
    exact hAp.of_injective ι (by
      intro x y hxy
      have hG :
          (((((x : AL) : L) : E) : M) : G) =
            (((((y : AL) : L) : E) : M) : G) :=
        congrArg (fun z : A => (z : G)) hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hG)
  exact le_sSup ⟨(inferInstance : AL.Normal), hALp⟩

private theorem CFSG.section11_complement_A_subgroupOf_hall_ge_le_omega_pCore_of_centralizes_tail
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hKPcomp :
      ((piCore ({q : Nat.Primes | p.val < q.val}) E).subgroupOf L).IsComplement'
        ((P.subtype hPleE : Subgroup E).subgroupOf L))
    (hAcent :
      (A.subgroupOf M).subgroupOf E ≤
        Subgroup.centralizer (piCore ({q : Nat.Primes | p.val < q.val}) E : Set E)) :
    (((A.subgroupOf M).subgroupOf E).subgroupOf L) ≤
      (omega₁ (G := pCore p.val L) (p := p.val)).map (pCore p.val L).subtype := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  rcases h11.A_rank_two with ⟨_hAcard, hAelem⟩
  let : IsElementaryAbelian p.val A := hAelem
  let AE : Subgroup E := (A.subgroupOf M).subgroupOf E
  let AL : Subgroup L := AE.subgroupOf L
  have hAL_le_core : AL ≤ pCore p.val L :=
    section11_complement_A_subgroupOf_hall_ge_le_pCore_of_centralizes_tail
      (G := G) h11 hPleE hKPcomp hAcent
  intro x hx
  have hxcore : x ∈ pCore p.val L := hAL_le_core hx
  refine Subgroup.mem_map.mpr ?_
  refine ⟨⟨x, hxcore⟩, ?_, rfl⟩
  rw [omega₁, omega]
  refine Subgroup.subset_closure ?_
  change (⟨x, hxcore⟩ : pCore p.val L) ^ (p.val ^ 1) = 1
  apply Subtype.ext
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  have hxA : (((x : L) : E) : M) ∈ A.subgroupOf M := by
    change ((x : L) : E) ∈ AE
    exact hx
  have hxAG : (((((x : L) : E) : M) : G) ∈ A) := by
    change (((x : L) : E) : M) ∈ A.subgroupOf M
    exact hxA
  have hxpG : (((((x : L) : E) : M) : G) ^ p.val = 1) :=
    elemPow_eq_one_of_isElementaryAbelian (p := p.val) (A := A)
      (((((x : L) : E) : M) : G)) hxAG
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact hxpG

private theorem CFSG.section11_complement_omega_pCore_le_A_subgroupOf_hall_ge
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hPLeL : (P.subtype hPleE : Subgroup E) ≤ L) :
    (omega₁ (G := pCore p.val L) (p := p.val)).map (pCore p.val L).subtype ≤
      (((A.subgroupOf M).subgroupOf E).subgroupOf L) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let PE : Subgroup E := P.subtype hPleE
  let AE : Subgroup E := (A.subgroupOf M).subgroupOf E
  let AL : Subgroup L := AE.subgroupOf L
  let PL : Subgroup L := PE.subgroupOf L
  have hcore_le_PL : pCore p.val L ≤ PL :=
    section11_complement_pCore_hall_ge_le_sylow (G := G) hPleE hPLeL
  have : IsMulCommutative (pCore p.val L) :=
    section11_complement_pCore_hall_ge_isMulCommutative h11 hPleE hPLeL
  have : IsMulCommutative (P : Subgroup M) := theorem_11_5 h11 P
  have hA_le_P : A.subgroupOf M ≤ (P : Subgroup M) :=
    section11_A_subgroupOf_le_sylow h11
  rintro x hx
  rcases Subgroup.mem_map.mp hx with ⟨xcore, hxΩ, rfl⟩
  have hxPL : (xcore : L) ∈ PL := hcore_le_PL xcore.property
  have hxP : ((((xcore : L) : E) : M) ∈ (P : Subgroup M)) := by
    change ((xcore : L) : E) ∈ PE
    change (xcore : L) ∈ PL
    exact hxPL
  have hxpow_core : xcore ^ p.val = 1 :=
    section11_mem_omegaOne_pow_eq_one_of_isMulCommutative hxΩ
  have hxpowL : (xcore : L) ^ p.val = 1 :=
    congrArg Subtype.val hxpow_core
  have hxpowG : (((((xcore : L) : E) : M) : G) ^ p.val = 1) := by
    simpa using congrArg (fun z : L => ((((z : E) : M) : G))) hxpowL
  have hxcent :
      ((((xcore : L) : E) : M) : G) ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a haA
    let xP : (P : Subgroup M) := ⟨(((xcore : L) : E) : M), hxP⟩
    let aM : M := ⟨a, h11.A_le_M haA⟩
    have haP : aM ∈ (P : Subgroup M) := by
      exact hA_le_P (by
        change (a : G) ∈ A
        exact haA)
    let aP : (P : Subgroup M) := ⟨aM, haP⟩
    have hcommM :
        (((xcore : L) : E) : M) * aM = aM * (((xcore : L) : E) : M) := by
      simpa [xP, aP] using
        (IsMulCommutative.is_comm (M := (P : Subgroup M))).comm xP aP
    simpa [aM] using congrArg (fun m : M => (m : G)) hcommM.symm
  have hxA : (((((xcore : L) : E) : M) : G) ∈ A) := by
    change (((((xcore : L) : E) : M) : G) ∈ (A : Set G))
    rw [h11.A_eq_centralizer_p_elements]
    exact ⟨hxcent, hxpowG⟩
  change ((xcore : L) : E) ∈ AE
  change (((xcore : L) : E) : M) ∈ A.subgroupOf M
  change ((((xcore : L) : E) : M) : G) ∈ A
  exact hxA

private theorem CFSG.section11_complement_A_subgroupOf_hall_ge_eq_omega_pCore_of_centralizes_tail
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hPLeL : (P.subtype hPleE : Subgroup E) ≤ L)
    (hKPcomp :
      ((piCore ({q : Nat.Primes | p.val < q.val}) E).subgroupOf L).IsComplement'
        ((P.subtype hPleE : Subgroup E).subgroupOf L))
    (hAcent :
      (A.subgroupOf M).subgroupOf E ≤
        Subgroup.centralizer (piCore ({q : Nat.Primes | p.val < q.val}) E : Set E)) :
    (((A.subgroupOf M).subgroupOf E).subgroupOf L) =
      (omega₁ (G := pCore p.val L) (p := p.val)).map (pCore p.val L).subtype := by
  refine le_antisymm ?_ ?_
  · exact
      section11_complement_A_subgroupOf_hall_ge_le_omega_pCore_of_centralizes_tail
        (G := G) h11 hPleE hKPcomp hAcent
  · exact
      section11_complement_omega_pCore_le_A_subgroupOf_hall_ge
        (G := G) h11 hPleE hPLeL

private theorem CFSG.section11_complement_A_subgroupOf_hall_ge_characteristic_of_centralizes_tail
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hPLeL : (P.subtype hPleE : Subgroup E) ≤ L)
    (hKPcomp :
      ((piCore ({q : Nat.Primes | p.val < q.val}) E).subgroupOf L).IsComplement'
        ((P.subtype hPleE : Subgroup E).subgroupOf L))
    (hAcent :
      (A.subgroupOf M).subgroupOf E ≤
        Subgroup.centralizer (piCore ({q : Nat.Primes | p.val < q.val}) E : Set E)) :
    (((A.subgroupOf M).subgroupOf E).subgroupOf L).Characteristic := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let ΩL : Subgroup L :=
    (omega₁ (G := pCore p.val L) (p := p.val)).map (pCore p.val L).subtype
  have : (pCore p.val L).Characteristic :=
    pCore_characteristic (G := L) (p := p.val)
  have : (omega₁ (G := pCore p.val L) (p := p.val)).Characteristic :=
    omega₁_characteristic (G := pCore p.val L) (p := p.val)
  have hΩchar : ΩL.Characteristic := by
    simpa [ΩL] using
      section11_characteristic_map_subtype_of_characteristic
        (G := L) (H := pCore p.val L)
        (K := omega₁ (G := pCore p.val L) (p := p.val))
  have hEq :
      (((A.subgroupOf M).subgroupOf E).subgroupOf L) = ΩL :=
    section11_complement_A_subgroupOf_hall_ge_eq_omega_pCore_of_centralizes_tail
      (G := G) h11 hPleE hPLeL hKPcomp hAcent
  rw [hEq]
  exact hΩchar

private theorem CFSG.section11_complement_A_normal_of_centralizes_tail
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hLnorm : L.Normal)
    (hPLeL : (P.subtype hPleE : Subgroup E) ≤ L)
    (hALeL : (A.subgroupOf M).subgroupOf E ≤ L)
    (hKPcomp :
      ((piCore ({q : Nat.Primes | p.val < q.val}) E).subgroupOf L).IsComplement'
        ((P.subtype hPleE : Subgroup E).subgroupOf L))
    (hAcent :
      (A.subgroupOf M).subgroupOf E ≤
        Subgroup.centralizer (piCore ({q : Nat.Primes | p.val < q.val}) E : Set E)) :
    ((A.subgroupOf M).subgroupOf E).Normal := by
  classical
  let AE : Subgroup E := (A.subgroupOf M).subgroupOf E
  let AL : Subgroup L := AE.subgroupOf L
  have : L.Normal := hLnorm
  have : AL.Characteristic :=
    section11_complement_A_subgroupOf_hall_ge_characteristic_of_centralizes_tail
      (G := G) h11 hPleE hPLeL hKPcomp hAcent
  have hmap_norm : (AL.map L.subtype).Normal := inferInstance
  have hmap_eq : AL.map L.subtype = AE := by
    simpa [AL, AE] using
      Subgroup.map_subgroupOf_eq_of_le (H := AE) (K := L) hALeL
  rwa [hmap_eq] at hmap_norm

private theorem CFSG.section11_complement_not_A_centralizes_tail
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E) {L : Subgroup E}
    (hLnorm : L.Normal)
    (hPLeL : (P.subtype hPleE : Subgroup E) ≤ L)
    (hALeL : (A.subgroupOf M).subgroupOf E ≤ L)
    (hAnotE : ¬ ((A.subgroupOf M).subgroupOf E).Normal)
    (hKPcomp :
      ((piCore ({q : Nat.Primes | p.val < q.val}) E).subgroupOf L).IsComplement'
        ((P.subtype hPleE : Subgroup E).subgroupOf L)) :
    ¬ (A.subgroupOf M).subgroupOf E ≤
        Subgroup.centralizer (piCore ({q : Nat.Primes | p.val < q.val}) E : Set E) := by
  intro hAcent
  exact hAnotE
    (section11_complement_A_normal_of_centralizes_tail
      (G := G) h11 hPleE hLnorm hPLeL hALeL hKPcomp hAcent)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_exists_A_tail_noncommuting_of_not_centralizes_tail
    {M A : Subgroup G} {p : Nat.Primes} {E : Subgroup M}
    (hnot :
      ¬ (A.subgroupOf M).subgroupOf E ≤
          Subgroup.centralizer (piCore ({q : Nat.Primes | p.val < q.val}) E : Set E)) :
    ∃ a : E, a ∈ (A.subgroupOf M).subgroupOf E ∧
      ∃ k : E, k ∈ piCore ({q : Nat.Primes | p.val < q.val}) E ∧ k * a ≠ a * k := by
  classical
  by_contra hnone
  apply hnot
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  by_contra hne
  exact hnone ⟨a, ha, k, hk, hne⟩


omit [IsMinCE G] in
private theorem CFSG.section11_complement_exists_A_invariant_tail_sylow
    {M A0 A : Subgroup G} {p q : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E) (_hp_lt_q : p.val < q.val) :
    ∃ Q : Sylow q.val (piCore ({r : Nat.Primes | p.val < r.val}) E),
      IsInvariant ((A.subgroupOf M).subgroupOf E)
        (piCore ({r : Nat.Primes | p.val < r.val}) E) (Q : Subgroup _) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have : Fact q.val.Prime := ⟨q.property⟩
  let K : Subgroup E := piCore ({r : Nat.Primes | p.val < r.val}) E
  let AE : Subgroup E := (A.subgroupOf M).subgroupOf E
  let PE : Subgroup E := P.subtype hPleE
  have hAE_norm_K : AE ≤ Subgroup.normalizer (K : Set E) :=
    Subgroup.le_normalizer_of_normal (H := K)
  have : Subgroup.Normalizes AE K := ⟨hAE_norm_K⟩
  have hAE_le_PE : AE ≤ PE := by
    intro x hx
    change ((x : E) : M) ∈ (P : Subgroup M)
    exact section11_A_subgroupOf_le_sylow h11 hx
  have hAEp : IsPGroup p.val AE :=
    IsPGroup.to_le (H := AE) (K := PE) (P.subtype hPleE).isPGroup' hAE_le_PE
  have : Fact (IsPGroup p.val AE) := ⟨hAEp⟩
  have hp_not_dvd_K : ¬ p.val ∣ Nat.card K := by
    intro hpdvd
    have hp_mem : p ∈ ({r : Nat.Primes | p.val < r.val}) :=
      piCore_isPiSubgroup (G := E) ({r : Nat.Primes | p.val < r.val}) p (by
        simpa [K] using hpdvd)
    exact (Nat.lt_irrefl p.val) hp_mem
  have hcop : Nat.Coprime p.val (Nat.card K) :=
    (p.property.coprime_iff_not_dvd).2 hp_not_dvd_K
  obtain ⟨Q, hQinv⟩ :=
    exists_invariant_sylow_of_pgroup_operator_coprime
      (G := K) (A := AE) (r := p.val) (p := q.val) hcop
  exact ⟨Q, hQinv⟩

omit [IsMinCE G] in
private theorem CFSG.section11_exists_prime_dvd_tail_centralizer_index_of_not_centralizes_tail
    {M A : Subgroup G} {p : Nat.Primes} {E : Subgroup M}
    (hnot :
      ¬ (A.subgroupOf M).subgroupOf E ≤
          Subgroup.centralizer (piCore ({q : Nat.Primes | p.val < q.val}) E : Set E)) :
    ∃ q : Nat.Primes,
      p.val < q.val ∧
        q.val ∣
          ((subgroupCentralizerIn
              (piCore ({r : Nat.Primes | p.val < r.val}) E)
              ((A.subgroupOf M).subgroupOf E)).subgroupOf
                (piCore ({r : Nat.Primes | p.val < r.val}) E)).index := by
  classical
  let K : Subgroup E := piCore ({r : Nat.Primes | p.val < r.val}) E
  let AE : Subgroup E := (A.subgroupOf M).subgroupOf E
  let C : Subgroup E := subgroupCentralizerIn K AE
  let CK : Subgroup K := C.subgroupOf K
  obtain ⟨a, haAE, k, hkK, hka_ne⟩ :=
    section11_exists_A_tail_noncommuting_of_not_centralizes_tail
      (G := G) (M := M) (A := A) (p := p) (E := E) hnot
  have hCK_ne_top : CK ≠ ⊤ := by
    intro htop
    have hkCK : (⟨k, by simpa [K] using hkK⟩ : K) ∈ CK := by
      simp [htop]
    have hkC : k ∈ C := by
      simpa [CK, C, K, Subgroup.mem_subgroupOf] using hkCK
    have hk_cent : k ∈ Subgroup.centralizer (AE : Set E) := hkC.2
    have hcomm : a * k = k * a :=
      Subgroup.mem_centralizer_iff.mp hk_cent a (by simpa [AE] using haAE)
    exact hka_ne hcomm.symm
  have hindex_ne_one : CK.index ≠ 1 := by
    intro hidx
    exact hCK_ne_top (Subgroup.index_eq_one.mp hidx)
  obtain ⟨q0, hq0prime, hq0dvd⟩ := Nat.exists_prime_and_dvd hindex_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  have hqK : q.val ∣ Nat.card K := by
    have hqidx' : q.val ∣ CK.index := by
      simpa [q] using hq0dvd
    exact hqidx'.trans (Subgroup.index_dvd_card (H := CK))
  have hqtail : p.val < q.val := by
    have hqtail' :=
      piCore_isPiSubgroup (G := E) ({r : Nat.Primes | p.val < r.val}) q (by
        simpa [K] using hqK)
    change p.val < q.val at hqtail'
    exact hqtail'
  exact ⟨q, hqtail, by simpa [K, AE, C, CK, q] using hq0dvd⟩

omit [IsMinCE G] in
private theorem CFSG.section11_complement_exists_noncentral_A_invariant_tail_sylow
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E)
    (hnot :
      ¬ (A.subgroupOf M).subgroupOf E ≤
          Subgroup.centralizer (piCore ({q : Nat.Primes | p.val < q.val}) E : Set E)) :
    ∃ q : Nat.Primes, ∃ Q : Sylow q.val (piCore ({r : Nat.Primes | p.val < r.val}) E),
      p.val < q.val ∧
        q.val ∣ Nat.card (piCore ({r : Nat.Primes | p.val < r.val}) E) ∧
          IsInvariant ((A.subgroupOf M).subgroupOf E)
            (piCore ({r : Nat.Primes | p.val < r.val}) E) (Q : Subgroup _) ∧
            ¬ (A.subgroupOf M).subgroupOf E ≤
              Subgroup.centralizer
                (((Q : Subgroup (piCore ({r : Nat.Primes | p.val < r.val}) E)).map
                    (piCore ({r : Nat.Primes | p.val < r.val}) E).subtype : Subgroup E) :
                  Set E) := by
  classical
  let K : Subgroup E := piCore ({r : Nat.Primes | p.val < r.val}) E
  let AE : Subgroup E := (A.subgroupOf M).subgroupOf E
  let C : Subgroup E := subgroupCentralizerIn K AE
  let CK : Subgroup K := C.subgroupOf K
  obtain ⟨q, hp_lt_q, hqidx⟩ :=
    section11_exists_prime_dvd_tail_centralizer_index_of_not_centralizes_tail
      (G := G) (M := M) (A := A) (p := p) (E := E) hnot
  have : Fact q.val.Prime := ⟨q.property⟩
  have hqidx' : q.val ∣ CK.index := by
    simpa [K, AE, C, CK] using hqidx
  have hqK : q.val ∣ Nat.card K := by
    exact hqidx'.trans (Subgroup.index_dvd_card (H := CK))
  obtain ⟨Q, hQinv⟩ :=
    section11_complement_exists_A_invariant_tail_sylow
      (G := G) (M := M) (A0 := A0) (A := A) (p := p) (q := q) (P := P)
      h11 hPleE hp_lt_q
  have hQ_not_cent :
      ¬ AE ≤
        Subgroup.centralizer (((Q : Subgroup K).map K.subtype : Subgroup E) : Set E) := by
    intro hAQcent
    have hQ_le_CK : (Q : Subgroup K) ≤ CK := by
      intro x hxQ
      have hxQmap : (x : E) ∈ ((Q : Subgroup K).map K.subtype : Subgroup E) :=
        Subgroup.mem_map.mpr ⟨x, hxQ, rfl⟩
      change (x : E) ∈ C
      refine ⟨x.property, ?_⟩
      change (x : E) ∈ Subgroup.centralizer (AE : Set E)
      rw [Subgroup.mem_centralizer_iff]
      intro a haAE
      have ha_cent :
          a ∈ Subgroup.centralizer (((Q : Subgroup K).map K.subtype : Subgroup E) : Set E) :=
        hAQcent haAE
      exact (Subgroup.mem_centralizer_iff.mp ha_cent (x : E) hxQmap).symm
    have hidx_dvd : CK.index ∣ (Q : Subgroup K).index :=
      Subgroup.index_dvd_of_le hQ_le_CK
    exact Q.not_dvd_index (hqidx'.trans hidx_dvd)
  exact ⟨q, Q, hp_lt_q, by simpa [K] using hqK, by simpa [K, AE] using hQinv,
    by simpa [K, AE] using hQ_not_cent⟩

omit [IsMinCE G] in
private theorem CFSG.section11_complement_A_normalizes_tail_sylow_ambient
    {M A0 A : Subgroup G} {p q : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E)
    {Q : Sylow q.val (piCore ({r : Nat.Primes | p.val < r.val}) E)}
    (hQinv :
      IsInvariant ((A.subgroupOf M).subgroupOf E)
        (piCore ({r : Nat.Primes | p.val < r.val}) E) (Q : Subgroup _)) :
    A ≤ Subgroup.normalizer
      (((((Q : Subgroup (piCore ({r : Nat.Primes | p.val < r.val}) E)).map
          (piCore ({r : Nat.Primes | p.val < r.val}) E).subtype : Subgroup E).map
            E.subtype : Subgroup M).map M.subtype : Subgroup G) : Set G) := by
  classical
  let K : Subgroup E := piCore ({r : Nat.Primes | p.val < r.val}) E
  let AE : Subgroup E := (A.subgroupOf M).subgroupOf E
  let QE : Subgroup E := (Q : Subgroup K).map K.subtype
  let QM : Subgroup M := QE.map E.subtype
  let QG : Subgroup G := QM.map M.subtype
  have : Fact p.val.Prime := ⟨p.property⟩
  have : Fact q.val.Prime := ⟨q.property⟩
  have hAE_norm_K : AE ≤ Subgroup.normalizer (K : Set E) :=
    Subgroup.le_normalizer_of_normal (H := K)
  have hAE_norm_QE : AE ≤ Subgroup.normalizer (QE : Set E) := by
    simpa [K, AE, QE] using
      section11_le_normalizer_map_of_isInvariant
        (G := E) (A := AE) (H := K) (K := (Q : Subgroup K)) hAE_norm_K hQinv
  change A ≤ Subgroup.normalizer (QG : Set G)
  refine subgroup_le_normalizer_of_conj_mem QG A ?_
  intro a x hxQG
  rcases Subgroup.mem_map.mp hxQG with ⟨xM, hxQM, rfl⟩
  rcases Subgroup.mem_map.mp hxQM with ⟨xE, hxQE, rfl⟩
  let aM : M := ⟨(a : G), h11.A_le_M a.property⟩
  have haE_mem : aM ∈ E := by
    have haM_A : aM ∈ A.subgroupOf M := by
      change (a : G) ∈ A
      exact a.property
    exact hPleE (section11_A_subgroupOf_le_sylow h11 haM_A)
  let aE : E := ⟨aM, haE_mem⟩
  have haE_AE : aE ∈ AE := by
    change (aE : M) ∈ A.subgroupOf M
    change ((aE : M) : G) ∈ A
    simp [aE, aM]
  have hx_conj_QE : aE * xE * aE⁻¹ ∈ QE :=
    (Subgroup.mem_normalizer_iff.mp (hAE_norm_QE haE_AE) (xE : E)).1 hxQE
  have hx_conj_QM : ((aE * xE * aE⁻¹ : E) : M) ∈ QM :=
    Subgroup.mem_map.mpr ⟨(aE * xE * aE⁻¹ : E), hx_conj_QE, rfl⟩
  refine Subgroup.mem_map.mpr ?_
  refine ⟨((aE * xE * aE⁻¹ : E) : M), hx_conj_QM, ?_⟩
  simp [aE, aM, mul_assoc]

omit [IsMinCE G] in
private theorem CFSG.section11_prime_mem_centralizer_of_tail_sylow_fixed_ne_bot
    {M A0 A : Subgroup G} {p q : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E)
    {Q : Sylow q.val (piCore ({r : Nat.Primes | p.val < r.val}) E)}
    (hCne :
      subgroupCentralizerIn
        (((Q : Subgroup (piCore ({r : Nat.Primes | p.val < r.val}) E)).map
          (piCore ({r : Nat.Primes | p.val < r.val}) E).subtype : Subgroup E))
        ((A.subgroupOf M).subgroupOf E) ≠ ⊥) :
    q ∈ subgroupPrimeSet (Subgroup.centralizer (A : Set G)) := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  let K : Subgroup E := piCore ({r : Nat.Primes | p.val < r.val}) E
  let AE : Subgroup E := (A.subgroupOf M).subgroupOf E
  let QE : Subgroup E := (Q : Subgroup K).map K.subtype
  let C : Subgroup E := subgroupCentralizerIn QE AE
  let CM : Subgroup M := C.map E.subtype
  let CG : Subgroup G := CM.map M.subtype
  have hQE_p : IsPGroup q.val QE := by
    simpa [K, QE] using
      IsPGroup.map (p := q.val) (H := (Q : Subgroup K)) Q.isPGroup' K.subtype
  have hC_le_QE : C ≤ QE := by
    intro x hx
    exact hx.1
  have hC_p : IsPGroup q.val C :=
    IsPGroup.to_le (H := C) (K := QE) hQE_p hC_le_QE
  have hC_nontrivial : Nontrivial C := by
    exact C.nontrivial_iff_ne_bot.mpr (by simpa [K, AE, QE, C] using hCne)
  have hqC : q.val ∣ Nat.card C := by
    rcases (IsPGroup.nontrivial_iff_card (p := q.val) (G := C) (hG := hC_p)).mp
        hC_nontrivial with ⟨n, hn_pos, hcard⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
    rw [hcard, pow_succ']
    exact dvd_mul_right q.val (q.val ^ m)
  have hcard_CM : Nat.card CM = Nat.card C := by
    simpa [CM] using
      Subgroup.card_map_of_injective (K := C) (f := E.subtype) E.subtype_injective
  have hcard_CG : Nat.card CG = Nat.card CM := by
    simpa [CG] using
      Subgroup.card_map_of_injective (K := CM) (f := M.subtype) M.subtype_injective
  have hqCG : q.val ∣ Nat.card CG := by
    simpa [hcard_CG, hcard_CM] using hqC
  have hCG_le_centA : CG ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xM, hxCM, rfl⟩
    rcases Subgroup.mem_map.mp hxCM with ⟨xE, hxC, rfl⟩
    change (xE : G) ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a haA
    let aM : M := ⟨a, h11.A_le_M haA⟩
    have haE_mem : aM ∈ E := by
      have haM_A : aM ∈ A.subgroupOf M := by
        change (a : G) ∈ A
        exact haA
      exact hPleE (section11_A_subgroupOf_le_sylow h11 haM_A)
    let aE : E := ⟨aM, haE_mem⟩
    have haE_AE : aE ∈ AE := by
      change (aE : M) ∈ A.subgroupOf M
      change ((aE : M) : G) ∈ A
      simpa [aE, aM] using haA
    have hx_cent : (xE : E) ∈ Subgroup.centralizer (AE : Set E) := hxC.2
    have hcommE : aE * xE = xE * aE :=
      Subgroup.mem_centralizer_iff.mp hx_cent aE haE_AE
    simpa [aE, aM] using congrArg (fun y : E => (((y : E) : M) : G)) hcommE
  let CGsub : Subgroup (Subgroup.centralizer (A : Set G)) := CG.subgroupOf (Subgroup.centralizer (A : Set G))
  have hcard_CGsub : Nat.card CGsub = Nat.card CG := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := CG)
      (K := Subgroup.centralizer (A : Set G)) hCG_le_centA).toEquiv
  have hqCGsub : q.val ∣ Nat.card CGsub := by
    simpa [hcard_CGsub] using hqCG
  exact hqCGsub.trans (Subgroup.card_subgroup_dvd_card CGsub)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_tail_sylow_centralizer_of_ambient
    {M A : Subgroup G} {p q : Nat.Primes} {E : Subgroup M}
    {Q : Sylow q.val (piCore ({r : Nat.Primes | p.val < r.val}) E)}
    (hAcent :
      A ≤ Subgroup.centralizer
        (((((Q : Subgroup (piCore ({r : Nat.Primes | p.val < r.val}) E)).map
          (piCore ({r : Nat.Primes | p.val < r.val}) E).subtype : Subgroup E).map
            E.subtype : Subgroup M).map M.subtype : Subgroup G) : Set G)) :
    (A.subgroupOf M).subgroupOf E ≤
      Subgroup.centralizer
        (((Q : Subgroup (piCore ({r : Nat.Primes | p.val < r.val}) E)).map
          (piCore ({r : Nat.Primes | p.val < r.val}) E).subtype : Subgroup E) : Set E) := by
  classical
  let K : Subgroup E := piCore ({r : Nat.Primes | p.val < r.val}) E
  let QE : Subgroup E := (Q : Subgroup K).map K.subtype
  let QM : Subgroup M := QE.map E.subtype
  let QG : Subgroup G := QM.map M.subtype
  intro a haA
  change a ∈ Subgroup.centralizer (QE : Set E)
  rw [Subgroup.mem_centralizer_iff]
  intro x hxQE
  let aG : G := ((a : E) : G)
  have haG : aG ∈ A := by
    change ((a : E) : M) ∈ A.subgroupOf M at haA
    change (((a : E) : M) : G) ∈ A at haA
    simpa [aG] using haA
  have hxQM : ((x : E) : M) ∈ QM :=
    Subgroup.mem_map.mpr ⟨x, hxQE, rfl⟩
  have hxQG : (((x : E) : M) : G) ∈ QG :=
    Subgroup.mem_map.mpr ⟨((x : E) : M), hxQM, rfl⟩
  have hcommG : (((x : E) : M) : G) * aG = aG * (((x : E) : M) : G) :=
    Subgroup.mem_centralizer_iff.mp (hAcent haG) _ hxQG
  exact Subtype.ext (Subtype.ext hcommG)

private def CFSG.section11StarShape (q : Nat.Primes) (Q : Subgroup G) : Prop :=
  IsCyclic Q ∨
    ∃ B : Subgroup Q, B ∈ section10RankTwoMaximalElementaryAbelianSubgroups q Q

private theorem CFSG.section11_prime_dvd_malphaSubgroup_card_of_alpha
    {M : Subgroup G} {q : Nat.Primes} (hM : M ∈ section9MaximalSubgroups G)
    (hqα : q ∈ section10AlphaPrimes M) :
    q.val ∣ Nat.card (section10MalphaSubgroup M) := by
  have hHall : IsHallSubgroup (section10AlphaPrimes M) (section10MalphaSubgroup M) :=
    (theorem_10_2_a hM).2
  have hqM : q.val ∣ Nat.card M := hqα.1
  have hprod :
      q.val ∣ (section10MalphaSubgroup M).index * Nat.card (section10MalphaSubgroup M) := by
    simpa [Subgroup.index_mul_card (H := section10MalphaSubgroup M)] using hqM
  rcases q.property.dvd_mul.mp hprod with hqidx | hqcard
  · exact False.elim ((hHall.p_in_pi_of_p_dvd_index q hqidx) hqα)
  · exact hqcard

private theorem CFSG.section11_prime_not_alpha_of_not_sigma
    {M : Subgroup G} {q : Nat.Primes} (hM : M ∈ section9MaximalSubgroups G)
    (hqσ : q ∉ section10SigmaPrimes M) :
    q ∉ section10AlphaPrimes M := by
  intro hqα
  have hqMα : q.val ∣ Nat.card (section10MalphaSubgroup M) :=
    section11_prime_dvd_malphaSubgroup_card_of_alpha hM hqα
  have hMα_le_Mσ : section10MalphaSubgroup M ≤ section10MsigmaSubgroup M :=
    (theorem_10_2_c hM).1
  have hqMσ : q.val ∣ Nat.card (section10MsigmaSubgroup M) :=
    hqMα.trans (Subgroup.card_dvd_of_le hMα_le_Mσ)
  exact hqσ ((theorem_10_2_b hM).2.p_in_pi_of_p_dvd_card q hqMσ)

private theorem CFSG.section11_primeRank_le_two_of_not_sigma
    {M : Subgroup G} {q : Nat.Primes} (hM : M ∈ section9MaximalSubgroups G)
    (hqσ : q ∉ section10SigmaPrimes M) (hqM : q.val ∣ Nat.card M) :
    primeRank q.val M ≤ 2 := by
  have hqα : q ∉ section10AlphaPrimes M :=
    section11_prime_not_alpha_of_not_sigma hM hqσ
  exact Nat.le_of_not_gt (by
    intro hgt
    exact hqα ⟨by simpa [subgroupPrimeSet] using hqM, hgt⟩)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_generatorRank_le_natCard
    (H : Type*) [Group H] [Finite H] :
    generatorRank H ≤ Nat.card H := by
  let : Fintype H := Fintype.ofFinite H
  obtain ⟨S, hS_card, _hS_top⟩ := Group.rank_spec H
  have hEq : generatorRank H = Group.rank H := generatorRank_eq_group_rank H
  rw [hEq, ← hS_card]
  simpa [Nat.card_eq_fintype_card] using Finset.card_le_univ S

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 2) :
    2 ≤ generatorRank A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by
          simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  rw [hA] at hcard_dvd
  have hle_rank : 2 ≤ Group.rank A :=
    (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_dvd
  simpa [generatorRank_eq_group_rank] using hle_rank

omit [IsMinCE G] in
private theorem CFSG.section11_primeRank_at_least_two_of_rank_two_subgroup
    {M B : Subgroup G} {q : Nat.Primes} (hBM : B ≤ M)
    (hB : B ∈ elementaryAbelianSubgroupsOfRank q.val 2 G) :
    2 ≤ primeRank q.val M := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  rcases hB with ⟨hBcard, hBelem⟩
  let Bsub : Subgroup M := B.subgroupOf M
  have hBsub_card : Nat.card Bsub = q.val ^ 2 := by
    simpa [Bsub, hBcard] using
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := B) (K := M) hBM).toEquiv
  have hBsub_elem : IsElementaryAbelian q.val Bsub := by
    let e : Bsub ≃* B := Subgroup.subgroupOfEquivOfLe (H := B) (K := M) hBM
    let : IsElementaryAbelian q.val B := hBelem
    refine
      { toIsMulCommutative := ?_
        exponent_dvd_p := ?_ }
    · refine { is_comm := ⟨fun x y => ?_⟩ }
      have hcomm : e x * e y = e y * e x := by
        exact (IsMulCommutative.is_comm (M := B)).comm (e x) (e y)
      simpa using congrArg e.symm hcomm
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro x
      have hxpow : e x ^ q.val = 1 := by
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p q.val B) (e x)
      simpa using congrArg e.symm hxpow
  have hBsub_gen : 2 ≤ generatorRank Bsub := by
    let : IsElementaryAbelian q.val Bsub := hBsub_elem
    exact section11_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
      (p := q.val) hBsub_card
  have hBsub_p : IsPGroup q.val Bsub := by
    let : IsElementaryAbelian q.val Bsub := hBsub_elem
    exact IsElementaryAbelian.isPGroup q.val Bsub
  have hBsub_comm : IsMulCommutative Bsub := by
    let : IsElementaryAbelian q.val Bsub := hBsub_elem
    exact hBsub_elem.toIsMulCommutative
  rw [primeRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card M, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section11_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  · exact ⟨Bsub, hBsub_p, hBsub_comm, hBsub_gen⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_rankTwoMaximal_subgroupOf_of_le
    {p : Nat.Primes} {A S : Subgroup G} (hAS : A ≤ S)
    (hArankTwo : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G)
    (hAmax : A ∈ maximalElementaryAbelianSubgroups p.val G) :
    A.subgroupOf S ∈ section10RankTwoMaximalElementaryAbelianSubgroups p S := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  rcases hArankTwo with ⟨hAcard, hAelem⟩
  rcases hAmax with ⟨_hAelem', hAmax'⟩
  have : IsElementaryAbelian p.val A := hAelem
  have hAsub_card : Nat.card (A.subgroupOf S) = p.val ^ 2 := by
    simpa [hAcard] using
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := S) hAS).toEquiv
  have hAsub_elem : IsElementaryAbelian p.val (A.subgroupOf S) := by
    let e : A.subgroupOf S ≃* A := Subgroup.subgroupOfEquivOfLe (H := A) (K := S) hAS
    refine
      { toIsMulCommutative := ?_
        exponent_dvd_p := ?_ }
    · refine { is_comm := ⟨fun x y => ?_⟩ }
      have hcomm : e x * e y = e y * e x := by
        exact (IsMulCommutative.is_comm (M := A)).comm (e x) (e y)
      simpa using congrArg e.symm hcomm
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro x
      have hxpow : e x ^ p.val = 1 := by
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p.val A) (e x)
      simpa using congrArg e.symm hxpow
  have hAsub_max : A.subgroupOf S ∈ maximalElementaryAbelianSubgroups p.val S := by
    refine ⟨hAsub_elem, ?_⟩
    intro B hAB hBelem
    let Bmap : Subgroup G := B.map S.subtype
    have hA_le_Bmap : A ≤ Bmap := by
      intro a ha
      let aS : A.subgroupOf S := ⟨⟨a, hAS ha⟩, ha⟩
      exact Subgroup.mem_map.mpr ⟨aS, hAB aS.2, rfl⟩
    have hBmap_elem : IsElementaryAbelian p.val Bmap := by
      let e : B ≃* Bmap := Subgroup.equivMapOfInjective
        (f := S.subtype) B S.subtype_injective
      let : IsElementaryAbelian p.val B := hBelem
      refine
        { toIsMulCommutative := ?_
          exponent_dvd_p := ?_ }
      · refine { is_comm := ⟨fun x y => ?_⟩ }
        have hcomm : e.symm x * e.symm y = e.symm y * e.symm x := by
          exact (IsMulCommutative.is_comm (M := B)).comm (e.symm x) (e.symm y)
        simpa using congrArg e hcomm
      · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
        intro x
        have hxpow : e.symm x ^ p.val = 1 := by
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p p.val B) (e.symm x)
        simpa using congrArg e hxpow
    have hEq : A = Bmap := hAmax' Bmap hA_le_Bmap hBmap_elem
    apply Subgroup.ext
    intro x
    constructor
    · intro hx
      have hxA : ((x : S) : G) ∈ A := hx
      rw [hEq] at hxA
      rcases Subgroup.mem_map.mp hxA with ⟨y, hyB, hyx⟩
      have : y = x := Subtype.ext hyx
      simpa [this] using hyB
    · intro hx
      have hxMap : ((x : S) : G) ∈ Bmap := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [← hEq] at hxMap
      exact hxMap
  exact ⟨⟨hAsub_card, hAsub_elem⟩, hAsub_max⟩

private theorem CFSG.section11_star_shape_of_noncyclic_tail_subgroup
    {M QG Qstar : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hqσ : q ∉ section10SigmaPrimes M)
    (hqM : q.val ∣ Nat.card M) (hQG_p : IsPGroup q.val QG)
    (hQG_le_M : QG ≤ M) (hQG_le_Qstar : QG ≤ Qstar)
    (hQG_noncyc : ¬ IsCyclic QG) :
    section11StarShape (G := G) q Qstar := by
  classical
  right
  have : Fact q.val.Prime := ⟨q.property⟩
  have hQG_nontrivial : Nontrivial QG := Nontrivial.of_not_isCyclic hQG_noncyc
  have hq_dvd_QG : q.val ∣ Nat.card QG := by
    rcases (IsPGroup.nontrivial_iff_card (p := q.val) (G := QG) (hG := hQG_p)).mp
        hQG_nontrivial with ⟨n, hn_pos, hcard⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
    rw [hcard, pow_succ']
    exact dvd_mul_right q.val (q.val ^ m)
  have hq_dvd_G : q.val ∣ Nat.card G :=
    hq_dvd_QG.trans (Subgroup.card_subgroup_dvd_card QG)
  have hq_odd : q.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hq_dvd_G
  let : Fact (IsPGroup q.val QG) := ⟨hQG_p⟩
  obtain ⟨B0, _hB0norm, hB0card, hB0elem⟩ :=
    lemma_4_5_a (R := QG) (p := q.val) hq_odd hQG_noncyc
  let BG : Subgroup G := B0.map QG.subtype
  have hBG_le_QG : BG ≤ QG := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨b, _hb, rfl⟩
    exact b.property
  have hBG_le_M : BG ≤ M := hBG_le_QG.trans hQG_le_M
  have hBG_le_Qstar : BG ≤ Qstar := hBG_le_QG.trans hQG_le_Qstar
  have hBGcard : Nat.card BG = q.val ^ 2 := by
    have hcard_map : Nat.card BG = Nat.card B0 := by
      simpa [BG] using
        Subgroup.card_map_of_injective (K := B0) (f := QG.subtype) QG.subtype_injective
    simpa [hB0card] using hcard_map
  have hBGelem : IsElementaryAbelian q.val BG := by
    let e : B0 ≃* BG := Subgroup.equivMapOfInjective
      (f := QG.subtype) B0 QG.subtype_injective
    let : IsElementaryAbelian q.val B0 := hB0elem
    refine
      { toIsMulCommutative := ?_
        exponent_dvd_p := ?_ }
    · refine { is_comm := ⟨fun x y => ?_⟩ }
      have hcomm : e.symm x * e.symm y = e.symm y * e.symm x := by
        exact (IsMulCommutative.is_comm (M := B0)).comm (e.symm x) (e.symm y)
      simpa using congrArg e hcomm
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro x
      have hxpow : e.symm x ^ q.val = 1 := by
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p q.val B0) (e.symm x)
      simpa using congrArg e hxpow
  have hBGrank : BG ∈ elementaryAbelianSubgroupsOfRank q.val 2 G :=
    ⟨hBGcard, hBGelem⟩
  have hprank_le : primeRank q.val M ≤ 2 :=
    section11_primeRank_le_two_of_not_sigma hM hqσ hqM
  have hprank_ge : 2 ≤ primeRank q.val M :=
    section11_primeRank_at_least_two_of_rank_two_subgroup hBG_le_M hBGrank
  have hprank : primeRank q.val M = 2 := le_antisymm hprank_le hprank_ge
  have hBGmax : BG ∈ maximalElementaryAbelianSubgroups q.val G :=
    (lemma_10_4_c (G := G) (M := M) (p := q) hM hqσ hprank).2 hBG_le_M hBGrank
  exact ⟨BG.subgroupOf Qstar,
    section11_rankTwoMaximal_subgroupOf_of_le
      (G := G) (p := q) hBG_le_Qstar hBGrank hBGmax⟩

private def CFSG.section11TailSylowInE
    {M : Subgroup G} {p q : Nat.Primes} {E : Subgroup M}
    (Q : Sylow q.val (piCore ({r : Nat.Primes | p.val < r.val}) E)) :
    Subgroup E :=
  (Q : Subgroup (piCore ({r : Nat.Primes | p.val < r.val}) E)).map
    (piCore ({r : Nat.Primes | p.val < r.val}) E).subtype

private def CFSG.section11TailSylowInM
    {M : Subgroup G} {p q : Nat.Primes} {E : Subgroup M}
    (Q : Sylow q.val (piCore ({r : Nat.Primes | p.val < r.val}) E)) :
    Subgroup M :=
  (section11TailSylowInE (G := G) (M := M) (p := p) (q := q) (E := E) Q).map
    E.subtype

private def CFSG.section11TailSylowInG
    {M : Subgroup G} {p q : Nat.Primes} {E : Subgroup M}
    (Q : Sylow q.val (piCore ({r : Nat.Primes | p.val < r.val}) E)) :
    Subgroup G :=
  (section11TailSylowInM (G := G) (M := M) (p := p) (q := q) (E := E) Q).map
    M.subtype

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_cyclic_pgroup_action_trivial_of_fixed_ne_bot
    {X A : Type*} [Group X] [Finite X] [Group A] [Finite A]
    [MulDistribMulAction A X] {q : ℕ} [Fact q.Prime]
    (hXp : IsPGroup q X) (hXcyc : IsCyclic X)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card X))
    (hfix_ne : fixedPointSubgroup A X ≠ ⊥) :
    ActsTrivially (A := A) (G := X) := by
  classical
  let : IsCyclic X := hXcyc
  let : CommGroup X := IsCyclic.commGroup
  have hcomm : IsMulCommutative X := { is_comm := ⟨fun a b => mul_comm a b⟩ }
  have hsolv : Group.IsSolvable X := Group.isSolvable_of_comm fun a b => mul_comm a b
  rcases IsPGroup.smul_mul_inv_trivial_or_surjective (p := q) hXp (K := A) hcop.symm with
    htriv | hsurj
  · intro a x
    have h := htriv x a
    simpa [mul_assoc] using congrArg (fun y => y * x) h
  · have hcomm_top : commutatorAction (A := A) (G := X) = ⊤ := by
      rw [commutatorAction_eq_closure]
      refine
        (Subgroup.eq_top_iff'
          (H := Subgroup.closure {x : X | ∃ a : A, ∃ g : X, x = g⁻¹ * (a • g)})).mpr ?_
      intro x
      obtain ⟨a, y, hy⟩ := hsurj x
      exact Subgroup.subset_closure ⟨a, y, by
        rw [← hy]
        exact mul_comm (a • y) y⁻¹⟩
    have hcompl :
        IsCompl (fixedPointSubgroup A X) (commutatorAction (A := A) (G := X)) :=
      proposition_1_6_d (G := X) (A := A) hsolv hcop hcomm
    have hfix_bot : fixedPointSubgroup A X = ⊥ := by
      simpa [hcomm_top] using hcompl.inf_eq_bot
    exact False.elim (hfix_ne hfix_bot)

omit [IsMinCE G] in
private theorem CFSG.section11_tail_sylow_noncyclic_of_fixed_ne_bot
    {M A0 A : Subgroup G} {p q : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E)
    {Q : Sylow q.val (piCore ({r : Nat.Primes | p.val < r.val}) E)}
    (hQinv :
      IsInvariant ((A.subgroupOf M).subgroupOf E)
        (piCore ({r : Nat.Primes | p.val < r.val}) E) (Q : Subgroup _))
    (hq_ne_p : q ≠ p)
    (hCne :
      subgroupCentralizerIn
        (((Q : Subgroup (piCore ({r : Nat.Primes | p.val < r.val}) E)).map
          (piCore ({r : Nat.Primes | p.val < r.val}) E).subtype : Subgroup E))
        ((A.subgroupOf M).subgroupOf E) ≠ ⊥)
    (hAQ_noncentral :
      ¬ (A.subgroupOf M).subgroupOf E ≤
        Subgroup.centralizer
          (((Q : Subgroup (piCore ({r : Nat.Primes | p.val < r.val}) E)).map
            (piCore ({r : Nat.Primes | p.val < r.val}) E).subtype : Subgroup E) : Set E)) :
    ¬ IsCyclic (section11TailSylowInG (G := G) (M := M) (p := p) (q := q) (E := E) Q) := by
  classical
  intro hQGcyc
  let K : Subgroup E := piCore ({r : Nat.Primes | p.val < r.val}) E
  let AE : Subgroup E := (A.subgroupOf M).subgroupOf E
  let QE : Subgroup E := (Q : Subgroup K).map K.subtype
  let QM : Subgroup M := QE.map E.subtype
  let QG : Subgroup G := QM.map M.subtype
  have : Fact p.val.Prime := ⟨p.property⟩
  have : Fact q.val.Prime := ⟨q.property⟩
  have hAE_norm_K : AE ≤ Subgroup.normalizer (K : Set E) :=
    Subgroup.le_normalizer_of_normal (H := K)
  have hAE_norm_QE : AE ≤ Subgroup.normalizer (QE : Set E) := by
    simpa [K, AE, QE] using
      section11_le_normalizer_map_of_isInvariant
        (G := E) (A := AE) (H := K) (K := (Q : Subgroup K)) hAE_norm_K hQinv
  let : Subgroup.Normalizes AE QE := ⟨hAE_norm_QE⟩
  have hQE_cyc : IsCyclic QE := by
    have hQGcyc' : IsCyclic QG := by
      change IsCyclic QG at hQGcyc
      exact hQGcyc
    have hQM_cyc : IsCyclic QM := by
      exact (Subgroup.equivMapOfInjective (f := M.subtype) QM M.subtype_injective).isCyclic.2
        hQGcyc'
    exact (Subgroup.equivMapOfInjective (f := E.subtype) QE E.subtype_injective).isCyclic.2
      hQM_cyc
  have hQE_p : IsPGroup q.val QE := by
    simpa [K, QE] using
      IsPGroup.map (p := q.val) (H := (Q : Subgroup K)) Q.isPGroup' K.subtype
  have hAE_le_PE : AE ≤ (P.subtype hPleE : Subgroup E) := by
    intro a ha
    change (a : M) ∈ (P : Subgroup M)
    exact section11_A_subgroupOf_le_sylow h11 ha
  have hAE_p : IsPGroup p.val AE :=
    IsPGroup.to_le (H := AE) (K := (P.subtype hPleE : Subgroup E))
      (P.subtype hPleE).isPGroup' hAE_le_PE
  have hp_ne_q_val : p.val ≠ q.val := by
    intro hpq
    exact hq_ne_p (Subtype.ext hpq.symm)
  have hcop : Nat.Coprime (Nat.card AE) (Nat.card QE) :=
    IsPGroup.coprime_card_of_ne p.val q.val hp_ne_q_val AE QE hAE_p hQE_p
  have hC_le_QE : subgroupCentralizerIn QE AE ≤ QE := by
    intro x hx
    exact hx.1
  have hfix_eq :
      fixedPointSubgroup AE QE = (subgroupCentralizerIn QE AE).subgroupOf QE := by
    simpa [AE, QE] using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn QE AE hAE_norm_QE
  have hfix_ne : fixedPointSubgroup AE QE ≠ ⊥ := by
    rw [hfix_eq]
    intro hbot
    apply hCne
    ext x
    constructor
    · intro hx
      have hxsub : (⟨x, hC_le_QE hx⟩ : QE) ∈ (subgroupCentralizerIn QE AE).subgroupOf QE := hx
      have hxbot : (⟨x, hC_le_QE hx⟩ : QE) ∈ (⊥ : Subgroup QE) := by
        simpa [hbot] using hxsub
      simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)
    · intro hx
      rw [Subgroup.mem_bot] at hx
      simp [hx]
  have htriv : ActsTrivially (A := AE) (G := QE) :=
    section11_cyclic_pgroup_action_trivial_of_fixed_ne_bot hQE_p hQE_cyc hcop hfix_ne
  apply hAQ_noncentral
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hfixed : (⟨a, ha⟩ : AE) • (⟨x, hx⟩ : QE) = ⟨x, hx⟩ :=
    htriv ⟨a, ha⟩ ⟨x, hx⟩
  have hconj : a * x * a⁻¹ = x := by
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc] using
      congrArg (fun y : QE => ((y : QE) : E)) hfixed
  simpa [mul_assoc] using (congrArg (fun y => y * a) hconj).symm

private theorem CFSG.section11_tail_sylow_fixed_point_free_of_star_shape
    {M A0 A : Subgroup G} {p q : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {E : Subgroup M}
    (hPleE : (P : Subgroup M) ≤ E)
    {Q : Sylow q.val (piCore ({r : Nat.Primes | p.val < r.val}) E)}
    (hq_ne_p : q ≠ p)
    (hAQ_noncentral :
      ¬ (A.subgroupOf M).subgroupOf E ≤
        Subgroup.centralizer
          (((Q : Subgroup (piCore ({r : Nat.Primes | p.val < r.val}) E)).map
            (piCore ({r : Nat.Primes | p.val < r.val}) E).subtype : Subgroup E) : Set E))
    {Qstar : Subgroup G}
    (hQstar : Qstar ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes))
    (hQG_le_Qstar : section11TailSylowInG (G := G) (M := M) (p := p) (q := q) (E := E) Q ≤ Qstar)
    (hQshape : section11StarShape (G := G) q Qstar) :
    subgroupCentralizerIn
      (((Q : Subgroup (piCore ({r : Nat.Primes | p.val < r.val}) E)).map
        (piCore ({r : Nat.Primes | p.val < r.val}) E).subtype : Subgroup E))
      ((A.subgroupOf M).subgroupOf E) = ⊥ := by
  classical
  by_contra hCne
  have hqC : q ∈ subgroupPrimeSet (Subgroup.centralizer (A : Set G)) :=
    section11_prime_mem_centralizer_of_tail_sylow_fixed_ne_bot
      (G := G) (M := M) (A0 := A0) (A := A) (p := p) (q := q) (P := P)
      h11 hPleE hCne
  obtain ⟨Pp, hA_le_Pp, hPp_le_cent_Qstar⟩ :=
    proposition_10_10_c (G := G) (p := p) (q := q) (Ne.symm hq_ne_p)
      h11.rankTwoMaximal hQstar hqC (by simpa [section11StarShape] using hQshape)
  let QG : Subgroup G := section11TailSylowInG (G := G) (M := M) (p := p) (q := q) (E := E) Q
  have hAcentQG : A ≤ Subgroup.centralizer (QG : Set G) := by
    intro a haA
    rw [Subgroup.mem_centralizer_iff]
    intro x hxQG
    exact
      Subgroup.mem_centralizer_iff.mp (hPp_le_cent_Qstar (hA_le_Pp haA))
        x (hQG_le_Qstar (by simpa [QG] using hxQG))
  have hAcentAmbient :
      A ≤ Subgroup.centralizer
        (((((Q : Subgroup (piCore ({r : Nat.Primes | p.val < r.val}) E)).map
          (piCore ({r : Nat.Primes | p.val < r.val}) E).subtype : Subgroup E).map
            E.subtype : Subgroup M).map M.subtype : Subgroup G) : Set G) := by
    simpa [QG, section11TailSylowInG, section11TailSylowInM, section11TailSylowInE]
      using hAcentQG
  apply hAQ_noncentral
  simpa using
    section11_tail_sylow_centralizer_of_ambient
      (G := G) (M := M) (A := A) (p := p) (q := q) (E := E)
      (Q := Q) hAcentAmbient

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_sylow_ne_bot_of_prime_dvd_card
    {H : Type*} [Group H] [Finite H] {q : Nat.Primes}
    (Q : Sylow q.val H) (hqH : q.val ∣ Nat.card H) :
    (Q : Subgroup H) ≠ ⊥ := by
  have : Fact q.val.Prime := ⟨q.property⟩
  have hqQ : q.val ∣ Nat.card (Q : Subgroup H) := by
    have hprod : q.val ∣ (Q : Subgroup H).index * Nat.card (Q : Subgroup H) := by
      simpa [Subgroup.index_mul_card (H := (Q : Subgroup H))] using hqH
    rcases q.property.dvd_mul.mp hprod with hqidx | hqcard
    · exact False.elim (Q.not_dvd_index hqidx)
    · exact hqcard
  intro hbot
  have hcard : Nat.card (Q : Subgroup H) = 1 := by simp [hbot]
  exact q.property.not_dvd_one (by simpa [hcard] using hqQ)

omit [IsMinCE G] in
private theorem CFSG.section11_rank_two_prime_order_product_decomposition
    {A A1 A2 : Subgroup G} {p : Nat.Primes}
    (hAcard : Nat.card A = p.val ^ 2)
    (hA1 : A1 ∈ section10PrimeOrderSubgroupsIn p A)
    (hA2 : A2 ∈ section10PrimeOrderSubgroupsIn p A)
    (hA12 : A1 ≠ A2) :
    ∀ x ∈ A, ∃ a1 ∈ A1, ∃ a2 ∈ A2, a1 * a2 = x := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let : Fintype A := Fintype.ofFinite A
  let : Fintype A1 := Fintype.ofFinite A1
  let : Fintype A2 := Fintype.ofFinite A2
  have hA1card : Nat.card A1 = p.val := hA1.2
  have hA2card : Nat.card A2 = p.val := hA2.2
  have hdisj_le : A1 ⊓ A2 ≤ ⊥ := by
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx_ne
    have hxA1_ne : (⟨x, hx.1⟩ : A1) ≠ 1 := by
      intro hx_one
      exact hx_ne (by simpa using congrArg Subtype.val hx_one)
    have hA1_le_A2 : A1 ≤ A2 := by
      intro y hy
      have hy_zpow :
          (⟨y, hy⟩ : A1) ∈ Subgroup.zpowers (⟨x, hx.1⟩ : A1) :=
        mem_zpowers_of_prime_card (G := A1) (p := p.val) (h := hA1card)
          (g := ⟨x, hx.1⟩) (g' := ⟨y, hy⟩) hxA1_ne
      rcases Subgroup.mem_zpowers_iff.mp hy_zpow with ⟨n, hn⟩
      have hy_eq : y = (((⟨x, hx.1⟩ : A1) ^ n : A1) : G) := by
        simpa using congrArg Subtype.val hn.symm
      rw [hy_eq]
      exact A2.zpow_mem hx.2 n
    have hEq : A1 = A2 :=
      Subgroup.eq_of_le_of_card_ge hA1_le_A2 (by
        have hA1card' : Fintype.card A1 = p.val := by
          rw [← Nat.card_eq_fintype_card, hA1card]
        have hA2card' : Fintype.card A2 = p.val := by
          rw [← Nat.card_eq_fintype_card, hA2card]
        omega)
    exact hA12 hEq
  let f : A1 × A2 → A := fun y =>
    ⟨(y.1 : G) * (y.2 : G), A.mul_mem (hA1.1 y.1.2) (hA2.1 y.2.2)⟩
  have hf_inj : Function.Injective f := by
    intro y z hyz
    have hprod : (y.1 : G) * (y.2 : G) = (z.1 : G) * (z.2 : G) :=
      congrArg Subtype.val hyz
    have hleft_eq :
        (z.1 : G)⁻¹ * (y.1 : G) = (z.2 : G) * (y.2 : G)⁻¹ := by
      calc
        (z.1 : G)⁻¹ * (y.1 : G)
            = (z.1 : G)⁻¹ * ((y.1 : G) * (y.2 : G)) * (y.2 : G)⁻¹ := by
                simp [mul_assoc]
        _ = (z.1 : G)⁻¹ * ((z.1 : G) * (z.2 : G)) * (y.2 : G)⁻¹ := by
                rw [hprod]
        _ = (z.2 : G) * (y.2 : G)⁻¹ := by
                simp
    have hleft_mem : (z.1 : G)⁻¹ * (y.1 : G) ∈ A1 ⊓ A2 := by
      refine ⟨A1.mul_mem (A1.inv_mem z.1.2) y.1.2, ?_⟩
      rw [hleft_eq]
      exact A2.mul_mem z.2.2 (A2.inv_mem y.2.2)
    have hleft_one : (z.1 : G)⁻¹ * (y.1 : G) = 1 := by
      simpa using hdisj_le hleft_mem
    have h1 : (y.1 : G) = (z.1 : G) := by
      have h := congrArg (fun t => (z.1 : G) * t) hleft_one
      simpa [mul_assoc] using h
    have h2 : (y.2 : G) = (z.2 : G) := by
      rw [h1] at hprod
      exact mul_left_cancel hprod
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hcard_f : Fintype.card (A1 × A2) = Fintype.card A := by
    have hA1card' : Fintype.card A1 = p.val := by
      simpa [Nat.card_eq_fintype_card] using hA1card
    have hA2card' : Fintype.card A2 = p.val := by
      simpa [Nat.card_eq_fintype_card] using hA2card
    have hAcard' : Fintype.card A = p.val ^ 2 := by
      simpa [Nat.card_eq_fintype_card] using hAcard
    simp [Fintype.card_prod, hA1card', hA2card', hAcard', pow_two]
  have hf_surj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcard_f⟩ |>.2
  intro x hxA
  obtain ⟨y, hy⟩ := hf_surj ⟨x, hxA⟩
  refine ⟨(y.1 : G), y.1.2, (y.2 : G), y.2.2, ?_⟩
  simpa [f] using congrArg Subtype.val hy

/-- Theorem 11.7. -/
public theorem CFSG.theorem_11_7
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    section10NormalIn (section10Msigma M ⊔ A) M := by
  classical
  by_contra hnot
  obtain ⟨E, hcomp, hPleE, L, hLchar, hLnorm, hLhall, hKleL, hPLeL, hALeL,
    hAnotE, hKPcomp⟩ :=
    section11_theorem_11_7_complement_setup h11 hnot
  have hA_not_centralizes_tail :
      ¬ (A.subgroupOf M).subgroupOf E ≤
          Subgroup.centralizer (piCore ({q : Nat.Primes | p.val < q.val}) E : Set E) :=
    section11_complement_not_A_centralizes_tail
      (G := G) h11 hPleE hLnorm hPLeL hALeL hAnotE hKPcomp
  obtain ⟨q, Q, hp_lt_q, hq_dvd_tail, hQinv, hAQ_noncentral⟩ :=
    section11_complement_exists_noncentral_A_invariant_tail_sylow
      (G := G) (M := M) (A0 := A0) (A := A) (p := p) (P := P) h11 hPleE
      hA_not_centralizes_tail
  have hQ_ne_bot : (Q : Subgroup (piCore ({r : Nat.Primes | p.val < r.val}) E)) ≠ ⊥ :=
    section11_sylow_ne_bot_of_prime_dvd_card Q hq_dvd_tail
  have hq_not_sigma : q ∉ section10SigmaPrimes M := by
    apply section11_prime_not_sigma_of_dvd_msigma_complement h11.maximal hcomp
    exact hq_dvd_tail.trans
      (Subgroup.card_subgroup_dvd_card (piCore ({r : Nat.Primes | p.val < r.val}) E))
  have hqM : q.val ∣ Nat.card M := by
    exact hq_dvd_tail.trans
      ((Subgroup.card_subgroup_dvd_card (piCore ({r : Nat.Primes | p.val < r.val}) E)).trans
        (Subgroup.card_subgroup_dvd_card E))
  have hq_ne_p : q ≠ p := by
    intro hqp
    rw [hqp] at hp_lt_q
    exact (Nat.lt_irrefl p.val) hp_lt_q
  let Ktail : Subgroup E := piCore ({r : Nat.Primes | p.val < r.val}) E
  let QE : Subgroup E := (Q : Subgroup Ktail).map Ktail.subtype
  let QM : Subgroup M := QE.map E.subtype
  let QG : Subgroup G := QM.map M.subtype
  have hAQG : A ≤ Subgroup.normalizer (QG : Set G) := by
    simpa [Ktail, QE, QM, QG] using
      section11_complement_A_normalizes_tail_sylow_ambient
        (G := G) (M := M) (A0 := A0) (A := A) (p := p) (q := q) (P := P)
        h11 hPleE hQinv
  have hQG_p : IsPGroup q.val QG := by
    have hQE_p : IsPGroup q.val QE := by
      simpa [Ktail, QE] using
        IsPGroup.map (p := q.val) (H := (Q : Subgroup Ktail)) Q.isPGroup' Ktail.subtype
    have hQM_p : IsPGroup q.val QM := by
      simpa [QE, QM] using
        IsPGroup.map (p := q.val) (H := QE) hQE_p E.subtype
    simpa [QM, QG] using
      IsPGroup.map (p := q.val) (H := QM) hQM_p M.subtype
  have hQGπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) QG :=
    section11_isPiSubgroup_singleton_of_isPGroup (G := G) hQG_p
  have hQGfam : QG ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    ⟨le_top, hQGπ, hAQG⟩
  obtain ⟨Qstar, hQstar, hQG_le_Qstar⟩ :=
    section8_exists_mem_section7HStarFamily_of_mem_family hQGfam
  have hC_Q_A_bot :
      subgroupCentralizerIn QE ((A.subgroupOf M).subgroupOf E) = ⊥ := by
    by_contra hCne
    have hQG_noncyc : ¬ IsCyclic QG := by
      change ¬ IsCyclic
        (section11TailSylowInG (G := G) (M := M) (p := p) (q := q) (E := E) Q)
      exact section11_tail_sylow_noncyclic_of_fixed_ne_bot
        (G := G) (M := M) (A0 := A0) (A := A) (p := p) (q := q) (P := P)
        h11 hPleE hQinv hq_ne_p (by simpa [Ktail, QE] using hCne) hAQ_noncentral
    have hQG_le_M : QG ≤ M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨m, _hm, rfl⟩
      exact m.2
    have hshape : section11StarShape (G := G) q Qstar :=
      section11_star_shape_of_noncyclic_tail_subgroup h11.maximal hq_not_sigma hqM
        hQG_p hQG_le_M hQG_le_Qstar hQG_noncyc
    have hQG_le_Qstar' :
        section11TailSylowInG (G := G) (M := M) (p := p) (q := q) (E := E) Q ≤ Qstar := by
      simpa [Ktail, QE, QM, QG, section11TailSylowInG, section11TailSylowInM,
        section11TailSylowInE] using hQG_le_Qstar
    have hbot :=
      section11_tail_sylow_fixed_point_free_of_star_shape
        (G := G) (M := M) (A0 := A0) (A := A) (p := p) (q := q) (P := P)
        h11 hPleE hq_ne_p hAQ_noncentral hQstar hQG_le_Qstar' hshape
    exact hCne (by simpa [Ktail, QE] using hbot)
  have : Fact q.val.Prime := ⟨q.property⟩
  have hHallTail : IsHallSubgroup ({r : Nat.Primes | p.val < r.val}) Ktail := by
    simpa [Ktail] using section11_complement_piCore_gt_isHall h11 hcomp hPleE
  have hQE_p : IsPGroup q.val QE := by
    simpa [Ktail, QE] using
      IsPGroup.map (p := q.val) (H := (Q : Subgroup Ktail)) Q.isPGroup' Ktail.subtype
  have hQM_p : IsPGroup q.val QM := by
    simpa [QE, QM] using
      IsPGroup.map (p := q.val) (H := QE) hQE_p E.subtype
  have hQE_not_dvd_index : ¬ q.val ∣ QE.index := by
    intro hdiv
    have hidx : QE.index = (Q : Subgroup Ktail).index * Ktail.index := by
      simpa [Ktail, QE] using
        (Subgroup.index_map_subtype (K := (Q : Subgroup Ktail)))
    rw [hidx] at hdiv
    rcases q.property.dvd_mul.mp hdiv with hQidx | hKidx
    · exact Q.not_dvd_index hQidx
    · exact (hHallTail.p_in_pi_of_p_dvd_index q hKidx) hp_lt_q
  have hQM_not_dvd_index : ¬ q.val ∣ QM.index := by
    intro hdiv
    have hidx : QM.index = QE.index * E.index := by
      simpa [QE, QM] using (Subgroup.index_map_subtype (K := QE))
    rw [hidx] at hdiv
    rcases q.property.dvd_mul.mp hdiv with hQEidx | hEidx
    · exact hQE_not_dvd_index hQEidx
    · exact ((section11_msigma_complement_isHall_sigma_compl h11.maximal hcomp).p_in_pi_of_p_dvd_index
          q hEidx) (by simpa using hq_not_sigma)
  let S : Sylow q.val M := IsPGroup.toSylow hQM_p hQM_not_dvd_index
  have hS_ambient : section10AmbientSylowSubgroup M S = QG := by
    simp [S, section10AmbientSylowSubgroup, QG, QM]
  have hQG_le_M : QG ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨m, _hm, rfl⟩
    exact m.2
  let Q0 : Subgroup G := (Subgroup.center QG).map QG.subtype
  have hQ0_le_QG : Q0 ≤ QG := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, _hz, rfl⟩
    exact z.2
  have hQ0_le_M : Q0 ≤ M := hQ0_le_QG.trans hQG_le_M
  have hQG_ne_bot : QG ≠ ⊥ := by
    rw [← hS_ambient]
    exact section11_ambientSylow_ne_bot_of_prime_dvd S hqM
  have hQ0_ne_bot : Q0 ≠ ⊥ := by
    have hQG_nontrivial : Nontrivial QG :=
      QG.nontrivial_iff_ne_bot.mpr hQG_ne_bot
    let : Nontrivial QG := hQG_nontrivial
    have hcenter_nontrivial : Nontrivial (Subgroup.center QG) :=
      IsPGroup.center_nontrivial (p := q.val) hQG_p
    obtain ⟨z, hz_ne⟩ := exists_ne (1 : Subgroup.center QG)
    intro hbot
    have hzQ0 : ((z : Subgroup.center QG) : G) ∈ Q0 :=
      Subgroup.mem_map.mpr ⟨z, z.2, rfl⟩
    have hzG_one : ((z : Subgroup.center QG) : G) = 1 := by
      simpa [hbot] using hzQ0
    apply hz_ne
    exact Subtype.ext (Subtype.ext hzG_one)
  have hQ0_p : IsPGroup q.val Q0 := by
    have hcenter_p : IsPGroup q.val (Subgroup.center QG) :=
      IsPGroup.to_le (H := Subgroup.center QG) (K := ⊤)
        (by simpa using hQG_p.to_subgroup (⊤ : Subgroup QG)) le_top
    simpa [Q0] using
      IsPGroup.map (p := q.val) (H := Subgroup.center QG) hcenter_p QG.subtype
  have hQ0π : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q0 :=
    section11_isPiSubgroup_singleton_of_isPGroup (G := G) hQ0_p
  have hQ0σc : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ Q0 :=
    section11_isPiSubgroup_sigma_compl_of_singleton hq_not_sigma hQ0π
  have hQ0p' : IsPiSubgroup (G := G) (section10PPrimeSet p) Q0 :=
    section11_isPiSubgroup_p_compl_of_singleton hq_ne_p hQ0π
  have hQ0_comm : IsMulCommutative Q0 := by
    let e : Subgroup.center QG ≃* Q0 :=
      Subgroup.equivMapOfInjective (f := QG.subtype) (Subgroup.center QG) QG.subtype_injective
    refine { is_comm := ⟨fun x y => ?_⟩ }
    have hcomm : e.symm x * e.symm y = e.symm y * e.symm x := by
      exact (IsMulCommutative.is_comm (M := Subgroup.center QG)).comm (e.symm x) (e.symm y)
    simpa using congrArg e hcomm
  have hQnormQ0 :
      Subgroup.normalizer (section10AmbientSylowSubgroup M S : Set G) ≤
        Subgroup.normalizer (Q0 : Set G) := by
    have : (Subgroup.center QG).Characteristic := Subgroup.centerCharacteristic
    have hnorm :
        Subgroup.normalizer (QG : Set G) ≤
          Subgroup.normalizer (Q0 : Set G) := by
      simpa [Q0] using
        section11_normalizer_le_normalizer_map_subtype_of_characteristic
          (G := G) QG (Subgroup.center QG)
    simpa [hS_ambient] using hnorm
  have hQG_norm_Q0 : Subgroup.normalizer (QG : Set G) ≤ Subgroup.normalizer (Q0 : Set G) := by
    simpa [hS_ambient] using hQnormQ0
  have hAQ0 : A ≤ Subgroup.normalizer (Q0 : Set G) :=
    hAQG.trans hQG_norm_Q0
  have hC_Q0_A_bot : subgroupCentralizerIn Q0 A = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxQG : x ∈ QG := hQ0_le_QG hx.1
    rcases Subgroup.mem_map.mp hxQG with ⟨xM, hxQM, rfl⟩
    rcases Subgroup.mem_map.mp hxQM with ⟨xE, hxQE, rfl⟩
    have hxCentQE : (xE : E) ∈ subgroupCentralizerIn QE ((A.subgroupOf M).subgroupOf E) := by
      refine ⟨hxQE, ?_⟩
      change (xE : E) ∈ Subgroup.centralizer (((A.subgroupOf M).subgroupOf E) : Set E)
      rw [Subgroup.mem_centralizer_iff]
      intro a haA
      have haG : (((a : E) : M) : G) ∈ A := by
        change ((a : E) : M) ∈ A.subgroupOf M at haA
        change (((a : E) : M) : G) ∈ A at haA
        exact haA
      have hcommG : (((a : E) : M) : G) * (((xE : E) : M) : G) =
          (((xE : E) : M) : G) * (((a : E) : M) : G) := by
        exact Subgroup.mem_centralizer_iff.mp hx.2 _ haG
      exact Subtype.ext (Subtype.ext hcommG)
    have hxQE_bot : (xE : E) ∈ (⊥ : Subgroup E) := by
      have : (xE : E) ∈ (⊥ : Subgroup E) := by
        simpa [hC_Q_A_bot] using hxCentQE
      exact this
    simpa using congrArg (fun y : E => (((y : E) : M) : G)) (Subgroup.mem_bot.mp hxQE_bot)
  have : Fact p.val.Prime := ⟨p.property⟩
  have hA_p : IsPGroup p.val A := by
    have : IsElementaryAbelian p.val A := h11.A_rank_two.2
    exact IsElementaryAbelian.isPGroup p.val A
  have hcop_A_Q0 : Nat.Coprime (Nat.card A) (Nat.card Q0) := by
    have hp_ne_q_val : p.val ≠ q.val := by
      intro hpq
      exact hq_ne_p (Subtype.ext hpq.symm)
    exact IsPGroup.coprime_card_of_ne p.val q.val hp_ne_q_val A Q0 hA_p hQ0_p
  let : Subgroup.Normalizes A Q0 := ⟨hAQ0⟩
  have hfix_Q0_A_bot : fixedPointSubgroup A Q0 = ⊥ := by
    have hfix_eq :
        fixedPointSubgroup A Q0 = (subgroupCentralizerIn Q0 A).subgroupOf Q0 := by
      simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Q0 A hAQ0
    rw [hfix_eq, hC_Q0_A_bot]
    ext x
    simp
  have hQ0_eq_comm_A : Q0 = ⁅Q0, A⁆ := by
    have hsolv_Q0 : Group.IsSolvable Q0 :=
      Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := Q0)).comm x y
    have hcompl :
        IsCompl (fixedPointSubgroup A Q0) (commutatorAction (A := A) (G := Q0)) :=
      proposition_1_6_d (G := Q0) (A := A) hsolv_Q0 hcop_A_Q0 hQ0_comm
    have hcomm_top : commutatorAction (A := A) (G := Q0) = ⊤ := by
      simpa [hfix_Q0_A_bot] using hcompl.sup_eq_top
    have hmap :
        (commutatorAction (A := A) (G := Q0)).map Q0.subtype = ⁅Q0, A⁆ :=
      commutatorAction_subgroup_conj_map_eq_commutator Q0 A hAQ0
    calc
      Q0 = (⊤ : Subgroup Q0).map Q0.subtype := by
        ext x
        constructor
        · intro hx
          exact ⟨⟨x, hx⟩, by simp, rfl⟩
        · rintro ⟨xQ0, _hx, rfl⟩
          exact xQ0.2
      _ = (commutatorAction (A := A) (G := Q0)).map Q0.subtype := by rw [hcomm_top]
      _ = ⁅Q0, A⁆ := hmap
  obtain ⟨A1, A2, hA1, hA2, hA12, hC1σ, hC2σ⟩ := corollary_11_6_c h11
  let N1 : Subgroup G := ⁅Q0, A1⁆
  let N2 : Subgroup G := ⁅Q0, A2⁆
  let Nsup : Subgroup G := N1 ⊔ N2
  have hA1_norm_Q0 : A1 ≤ subgroupNormalizerIn M (Q0 : Set G) := by
    intro x hx
    exact ⟨hAQ0 (hA1.1 hx), h11.A_le_M (hA1.1 hx)⟩
  have hA2_norm_Q0 : A2 ≤ subgroupNormalizerIn M (Q0 : Set G) := by
    intro x hx
    exact ⟨hAQ0 (hA2.1 hx), h11.A_le_M (hA2.1 hx)⟩
  have hN1_data :=
    proposition_10_11_d (G := G) (M := M) (K := Q0) (P := A1) (p := p)
      h11.maximal hQ0_le_M hQ0σc h11.not_sigma hA1_norm_Q0 hA1.2 hC1σ
      hQ0_comm hQ0p'
  have hN2_data :=
    proposition_10_11_d (G := G) (M := M) (K := Q0) (P := A2) (p := p)
      h11.maximal hQ0_le_M hQ0σc h11.not_sigma hA2_norm_Q0 hA2.2 hC2σ
      hQ0_comm hQ0p'
  have hN1_normIn : section10NormalIn N1 M := by
    simpa [N1] using hN1_data.2.1
  have hN2_normIn : section10NormalIn N2 M := by
    simpa [N2] using hN2_data.2.1
  have hN1_le_M : N1 ≤ M := hN1_normIn.1
  have hN2_le_M : N2 ≤ M := hN2_normIn.1
  have hNsup_le_M : Nsup ≤ M := by
    simpa [Nsup] using sup_le hN1_le_M hN2_le_M
  have hNsup_norm : (Nsup.subgroupOf M).Normal := by
    have : (N1.subgroupOf M).Normal := hN1_normIn.2
    have : (N2.subgroupOf M).Normal := hN2_normIn.2
    simpa [Nsup] using
      (by
        rw [Subgroup.subgroupOf_sup hN1_le_M hN2_le_M]
        infer_instance : ((N1 ⊔ N2).subgroupOf M).Normal)
  have hN1_le_Q0 : N1 ≤ Q0 := by
    change ⁅Q0, A1⁆ ≤ Q0
    rw [Subgroup.commutator_le]
    intro x hx a ha
    have ha_norm : a ∈ Subgroup.normalizer (Q0 : Set G) := hAQ0 (hA1.1 ha)
    have hxinv_conj : a * x⁻¹ * a⁻¹ ∈ Q0 :=
      (Subgroup.mem_normalizer_iff.mp ha_norm x⁻¹).1 (Q0.inv_mem hx)
    have hcomm_eq : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [hcomm_eq]
    exact Q0.mul_mem hx hxinv_conj
  have hN2_le_Q0 : N2 ≤ Q0 := by
    change ⁅Q0, A2⁆ ≤ Q0
    rw [Subgroup.commutator_le]
    intro x hx a ha
    have ha_norm : a ∈ Subgroup.normalizer (Q0 : Set G) := hAQ0 (hA2.1 ha)
    have hxinv_conj : a * x⁻¹ * a⁻¹ ∈ Q0 :=
      (Subgroup.mem_normalizer_iff.mp ha_norm x⁻¹).1 (Q0.inv_mem hx)
    have hcomm_eq : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [hcomm_eq]
    exact Q0.mul_mem hx hxinv_conj
  have hNsup_le_Q0 : Nsup ≤ Q0 := by
    simpa [Nsup] using sup_le hN1_le_Q0 hN2_le_Q0
  have hcomm_A_le_Nsup : ⁅Q0, A⁆ ≤ Nsup := by
    rw [Subgroup.commutator_le]
    intro x hx a ha
    obtain ⟨a1, ha1, a2, ha2, ha12⟩ :=
      section11_rank_two_prime_order_product_decomposition h11.A_rank_two.1 hA1 hA2 hA12 a ha
    rw [← ha12]
    have hc1 : ⁅x, a1⁆ ∈ Nsup := by
      exact Subgroup.mem_sup_left (by
        exact Subgroup.commutator_mem_commutator hx ha1)
    have hc2_N2 : ⁅x, a2⁆ ∈ N2 := by
      exact Subgroup.commutator_mem_commutator hx ha2
    have hc2 : ⁅x, a2⁆ ∈ Nsup := Subgroup.mem_sup_right hc2_N2
    have hconj_c2 : a1 * ⁅x, a2⁆ * a1⁻¹ ∈ Nsup := by
      have ha1M : a1 ∈ M := h11.A_le_M (hA1.1 ha1)
      have hc2M : ⁅x, a2⁆ ∈ M := hNsup_le_M hc2
      have hc2_sub : (⟨⁅x, a2⁆, hc2M⟩ : M) ∈ Nsup.subgroupOf M := hc2
      have hconj_sub :=
        Subgroup.Normal.conj_mem hNsup_norm (⟨⁅x, a2⁆, hc2M⟩ : M) hc2_sub
          (⟨a1, ha1M⟩ : M)
      change ((a1 * ⁅x, a2⁆) * a1⁻¹) ∈ Nsup
      exact Subgroup.mem_subgroupOf.mp hconj_sub
    have hcomm_eq : ⁅x, a1 * a2⁆ = ⁅x, a1⁆ * (a1 * ⁅x, a2⁆ * a1⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [hcomm_eq]
    exact Nsup.mul_mem hc1 hconj_c2
  have hQ0_eq_Nsup : Q0 = Nsup := by
    apply le_antisymm
    · calc
        Q0 = ⁅Q0, A⁆ := hQ0_eq_comm_A
        _ ≤ Nsup := hcomm_A_le_Nsup
    · exact hNsup_le_Q0
  have hQ0_normM : (Q0.subgroupOf M).Normal := by
    simpa [hQ0_eq_Nsup] using hNsup_norm
  have : (Q0.subgroupOf M).Normal := hQ0_normM
  exact
    section11_sigma_contradiction_of_sylow_normalizer_preserves_normal
      (G := G) (M := M) (Q0 := Q0) (q := q) S h11.maximal hq_not_sigma hqM
      hQ0_le_M hQ0_ne_bot hQnormQ0

end Section11
