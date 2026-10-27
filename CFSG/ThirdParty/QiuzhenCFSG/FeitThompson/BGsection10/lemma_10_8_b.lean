module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_8_a
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section10_isNilpotent_of_hasNormalPComplements
    {H : Type*} [Group H] [Finite H]
    (hcomp : ∀ p : Nat.Primes, p.val ∣ Nat.card H → HasNormalPComplement p.val H) :
    Group.IsNilpotent H := by
  classical
  have hnil_iff := (Group.isNilpotent_of_finite_tfae (G := H)).out 1 4
  rw [hnil_iff]
  intro p hp P
  by_cases hpH : p ∣ Nat.card H
  · let I : Type := {q : Nat.Primes // q.val ∣ Nat.card H ∧ q.val ≠ p}
    let C : Subgroup H := ⨅ q : I, pPrimeCore q.val H
    have hP_le_C : (P : Subgroup H) ≤ C := by
      intro x hx
      rw [Subgroup.mem_iInf]
      intro q
      have : Fact q.val.val.Prime := ⟨q.val.property⟩
      have hq_not_dvd_P : ¬ q.val.val ∣ Nat.card (P : Subgroup H) := by
        intro hq_dvd
        rcases P.isPGroup'.exists_card_eq with ⟨n, hcardP⟩
        have hq_dvd_pow : q.val.val ∣ p ^ n := by
          simpa [hcardP] using hq_dvd
        have hq_eq_p : q.val.val = p :=
          Nat.prime_eq_prime_of_dvd_pow q.val.property hp.out hq_dvd_pow
        exact q.property.2 hq_eq_p
      exact section10_subgroup_le_pPrimeCore_of_hasNormalPComplement_of_not_dvd
        (H := H) (p := q.val.val) (B := (P : Subgroup H))
        (hcomp q.val q.property.1) hq_not_dvd_P hx
    have hCnormal : C.Normal := by
      simpa [C, I] using
        Subgroup.normal_iInf_normal (fun q : I =>
          (inferInstance : (pPrimeCore q.val.val H).Normal))
    have hCp : IsPGroup p C := by
      refine (IsPGroup.iff_card (p := p) (G := C)).2 ?_
      have hcard_pos : Nat.card C ≠ 0 := Nat.card_pos.ne'
      refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hcard_pos ?_⟩
      intro q hqprime hq_dvd
      by_cases hqp : q = p
      · exact hqp
      · exfalso
        let q' : Nat.Primes := ⟨q, hqprime⟩
        have hqH : q'.val ∣ Nat.card H :=
          hq_dvd.trans (Subgroup.card_subgroup_dvd_card C)
        let iq : I := ⟨q', hqH, by simpa [q'] using hqp⟩
        have hC_le_core : C ≤ pPrimeCore q H := by
          change C ≤ (fun q : I => pPrimeCore q.val.val H) iq
          exact iInf_le _ iq
        have hq_core : q ∣ Nat.card (pPrimeCore q H) :=
          hq_dvd.trans (Subgroup.card_dvd_of_le hC_le_core)
        have : Fact q.Prime := ⟨hqprime⟩
        exact ((hqprime.coprime_iff_not_dvd).1
          (pPrimeCore_coprime_card (G := H) (p := q))) hq_core
    have hC_eq_P : C = (P : Subgroup H) :=
      P.is_maximal' hCp hP_le_C
    rw [← hC_eq_P]
    exact hCnormal
  · have hPbot : (P : Subgroup H) = ⊥ := by
      rcases P.isPGroup'.card_eq_or_dvd with hcard | hp_dvd_P
      · exact (Subgroup.card_eq_one (H := (P : Subgroup H))).mp hcard
      · exact False.elim
          (hpH (hp_dvd_P.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup H))))
    rw [hPbot]
    infer_instance

private theorem CFSG.section10_hasNormalPComplement_quotient_of_le_pPrimeCore
    {H : Type*} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    {p : ℕ} [Fact p.Prime]
    (hN_le_core : N ≤ pPrimeCore p H) (hcomp : HasNormalPComplement p H) :
    HasNormalPComplement p (H ⧸ N) := by
  classical
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  let C : Subgroup (H ⧸ N) := (pPrimeCore p H).map q
  have hCnormal : C.Normal :=
    Subgroup.Normal.map (inferInstance : (pPrimeCore p H).Normal) q
      (QuotientGroup.mk'_surjective N)
  have hCcop : Nat.Coprime p (Nat.card C) := by
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_map_dvd (H := pPrimeCore p H) q)
      (pPrimeCore_coprime_card (G := H) (p := p))
  have hquot_core_p : IsPGroup p (H ⧸ pPrimeCore p H) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
      (p := p) (H := H) hcomp
  have hquot_p : IsPGroup p ((H ⧸ N) ⧸ C) := by
    let e : (H ⧸ N) ⧸ C ≃* H ⧸ pPrimeCore p H :=
      QuotientGroup.quotientQuotientEquivQuotient
        (N := N) (M := pPrimeCore p H) hN_le_core
    exact hquot_core_p.of_equiv e.symm
  exact ⟨C, hCnormal, hCcop, hquot_p⟩

private theorem CFSG.section10_quotient_mbeta_hasNormalPComplement
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {K : Subgroup M} (hNleK : section10MbetaSubgroup M ≤ K)
    (hKleD : K ≤ derivedSubgroup M) {p : Nat.Primes}
    (hp_dvd : p.val ∣ Nat.card (K ⧸ (section10MbetaSubgroup M).subgroupOf K)) :
    HasNormalPComplement p.val (K ⧸ (section10MbetaSubgroup M).subgroupOf K) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let N : Subgroup M := section10MbetaSubgroup M
  let Nsub : Subgroup K := N.subgroupOf K
  have hNHall : IsHallSubgroup (section10BetaPrimes M) N :=
    section10_mbetaSubgroup_isHall hM
  have hp_dvd_K : p.val ∣ Nat.card K :=
    hp_dvd.trans (Subgroup.card_quotient_dvd_card (s := Nsub))
  have hpM : p ∈ subgroupPrimeSet M := by
    exact hp_dvd_K.trans (Subgroup.card_subgroup_dvd_card K)
  have hp_dvd_Nidx : p.val ∣ N.index := by
    have hp_dvd_Nsubidx : p.val ∣ Nsub.index := by
      simpa [Nsub, Subgroup.index_eq_card] using hp_dvd
    have hmap : Nsub.map K.subtype = N := by
      ext x
      simp [Nsub, N, hNleK]
    have hidx : N.index = Nsub.index * K.index := by
      have h := Subgroup.index_map_subtype (H := K) (K := Nsub)
      simpa [hmap] using h
    exact hp_dvd_Nsubidx.trans ⟨K.index, hidx⟩
  have hpβ : p ∉ section10BetaPrimes M :=
    hNHall.p_in_pi_of_p_dvd_index p hp_dvd_Nidx
  have hcompD : HasNormalPComplement p.val (derivedSubgroup M) :=
    (section10_normalPComplements_of_not_mem_beta hM hpM hpβ).1
  have hcompK : HasNormalPComplement p.val K :=
    hasNormalPComplement_of_le (G := M) (p := p.val) hKleD hcompD
  have hp_not_dvd_Nsub : ¬ p.val ∣ Nat.card Nsub := by
    intro hpNsub
    have hcard : Nat.card Nsub = Nat.card N := by
      simpa [Nsub, N] using
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := N) (K := K) hNleK).toEquiv
    have hpN : p.val ∣ Nat.card N := by
      simpa [hcard] using hpNsub
    exact hpβ (hNHall.p_in_pi_of_p_dvd_card p hpN)
  have hNsub_le_core : Nsub ≤ pPrimeCore p.val K :=
    section10_subgroup_le_pPrimeCore_of_hasNormalPComplement_of_not_dvd
      (H := K) (p := p.val) (B := Nsub) hcompK hp_not_dvd_Nsub
  exact section10_hasNormalPComplement_quotient_of_le_pPrimeCore
    (H := K) (N := Nsub) (p := p.val) hNsub_le_core hcompK

public theorem CFSG.section10_quotient_mbeta_nilpotent_of_le_derived
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {K : Subgroup M} (hNleK : section10MbetaSubgroup M ≤ K)
    (hKleD : K ≤ derivedSubgroup M) :
    Group.IsNilpotent (K ⧸ (section10MbetaSubgroup M).subgroupOf K) := by
  classical
  exact section10_isNilpotent_of_hasNormalPComplements
    (H := K ⧸ (section10MbetaSubgroup M).subgroupOf K)
    (fun p hp_dvd =>
      section10_quotient_mbeta_hasNormalPComplement
        (G := G) hM hNleK hKleD hp_dvd)

private theorem CFSG.section10_hasNilpotentHallSubgroup_of_normal_hall_quotient_nilpotent
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes}
    {K N : Subgroup H} (_hNK : N ≤ K)
    (hNnormalK : (N.subgroupOf K).Normal)
    (hNHallK : IsHallSubgroup π (N.subgroupOf K))
    (hquotNil : Group.IsNilpotent (K ⧸ N.subgroupOf K)) :
    section10HasNilpotentHallSubgroup πᶜ K := by
  classical
  let Nsub : Subgroup K := N.subgroupOf K
  haveI : Nsub.Normal := by
    simpa [Nsub] using hNnormalK
  obtain ⟨C, hcomp⟩ :=
    Subgroup.exists_right_complement'_of_coprime
      (N := Nsub) hNHallK.card_coprime_index
  let L : Subgroup H := C.map K.subtype
  have hLK : L ≤ K := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hLsub_eq : L.subgroupOf K = C := by
    simpa [L] using (subgroupOf_map_subtype_eq (K := K) C)
  have hCHall : IsHallSubgroup πᶜ C := by
    refine isHallSubgroup_of (G := K) (π := πᶜ) (H := C) ?_ ?_
    · intro q hq_dvd_C
      rw [Set.mem_compl_iff]
      have hq_dvd_Nidx : q.val ∣ Nsub.index := by
        have hidx : Nsub.index = Nat.card C := hcomp.symm.index_eq_card
        simpa [hidx] using hq_dvd_C
      exact hNHallK.p_in_pi_of_p_dvd_index q hq_dvd_Nidx
    · intro q hqπc hq_dvd_Cidx
      have hq_dvd_N : q.val ∣ Nat.card Nsub := by
        have hidx : C.index = Nat.card Nsub := hcomp.index_eq_card
        simpa [hidx] using hq_dvd_Cidx
      exact hqπc (hNHallK.p_in_pi_of_p_dvd_card q hq_dvd_N)
  have hCnil : Group.IsNilpotent C := by
    letI : Group.IsNilpotent (K ⧸ Nsub) := hquotNil
    let e : K ⧸ Nsub ≃* C := hcomp.symm.QuotientMulEquiv
    exact Group.nilpotent_of_mulEquiv (G := K ⧸ Nsub) (G' := C) e
  have hLnil : Group.IsNilpotent L := by
    let e : C ≃* L := Subgroup.equivMapOfInjective C K.subtype K.subtype_injective
    letI : Group.IsNilpotent C := hCnil
    exact Group.nilpotent_of_mulEquiv (G := C) (G' := L) e
  exact ⟨L, hLK, by simpa [hLsub_eq] using hCHall, hLnil⟩

/-- Lemma 10.8(b). -/
public theorem CFSG.lemma_10_8_b
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    section10HasNilpotentHallSubgroup (section10BetaPrimes M)ᶜ (derivedSubgroup M) ∧
      section10HasNilpotentHallSubgroup (section10BetaPrimes M)ᶜ (section10MsigmaSubgroup M) := by
  classical
  let N : Subgroup M := section10MbetaSubgroup M
  let D : Subgroup M := derivedSubgroup M
  let S : Subgroup M := section10MsigmaSubgroup M
  have hNleS : N ≤ S := by
    simpa [N, S] using section10_mbetaSubgroup_le_msigmaSubgroup hM
  have hSleD : S ≤ D := by
    simpa [S, D] using section10_msigmaSubgroup_le_derivedSubgroup hM
  have hNleD : N ≤ D := hNleS.trans hSleD
  have hNHall : IsHallSubgroup (section10BetaPrimes M) N := by
    simpa [N] using section10_mbetaSubgroup_isHall hM
  have hNnormalD : (N.subgroupOf D).Normal := by
    simpa [N, D] using (Subgroup.Normal.subgroupOf (inferInstance : N.Normal) D)
  have hNnormalS : (N.subgroupOf S).Normal := by
    simpa [N, S] using (Subgroup.Normal.subgroupOf (inferInstance : N.Normal) S)
  have hNHallD : IsHallSubgroup (section10BetaPrimes M) (N.subgroupOf D) :=
    hNHall.subgroupOf hNleD
  have hNHallS : IsHallSubgroup (section10BetaPrimes M) (N.subgroupOf S) :=
    hNHall.subgroupOf hNleS
  have hquotD : Group.IsNilpotent (D ⧸ N.subgroupOf D) :=
    section10_quotient_mbeta_nilpotent_of_le_derived
      (G := G) hM hNleD (by simp [D])
  have hquotS : Group.IsNilpotent (S ⧸ N.subgroupOf S) :=
    section10_quotient_mbeta_nilpotent_of_le_derived
      (G := G) hM hNleS hSleD
  exact
    ⟨section10_hasNilpotentHallSubgroup_of_normal_hall_quotient_nilpotent
        (H := M) hNleD hNnormalD hNHallD hquotD,
      section10_hasNilpotentHallSubgroup_of_normal_hall_quotient_nilpotent
        (H := M) hNleS hNnormalS hNHallS hquotS⟩
