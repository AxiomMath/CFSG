module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_11_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_11_b
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_pCore_characteristic
    {R : Type*} [Group R] {p : ℕ} [Fact p.Prime] :
    (pCore p R).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  have hmap_le : (pCore p R).map φ.toMonoidHom ≤ pCore p R := by
    exact le_sSup ⟨Subgroup.Normal.map (H := pCore p R) inferInstance
      φ.toMonoidHom φ.surjective,
      IsPGroup.map (p := p) (H := pCore p R)
        (pCore_isPGroup (G := R) (p := p)) φ.toMonoidHom⟩
  have hsymm_le : (pCore p R).map φ.symm.toMonoidHom ≤ pCore p R := by
    exact le_sSup ⟨Subgroup.Normal.map (H := pCore p R) inferInstance
      φ.symm.toMonoidHom φ.symm.surjective,
      IsPGroup.map (p := p) (H := pCore p R)
        (pCore_isPGroup (G := R) (p := p)) φ.symm.toMonoidHom⟩
  have hmap_symm :
      ((pCore p R).map φ.symm.toMonoidHom).map φ.toMonoidHom = pCore p R := by
    rw [Subgroup.map_map]
    have hcomp : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id R := by
      ext x
      simp
    rw [hcomp]
    simp
  exact le_antisymm hmap_le <| by
    calc
      pCore p R = ((pCore p R).map φ.symm.toMonoidHom).map φ.toMonoidHom :=
        hmap_symm.symm
      _ ≤ (pCore p R).map φ.toMonoidHom := Subgroup.map_mono hsymm_le

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_pSubgroup_le_pCore_of_nilpotent
    {R : Type*} [Group R] [Finite R] [Group.IsNilpotent R]
    {p : ℕ} [Fact p.Prime] {B : Subgroup R} (hBp : IsPGroup p B) :
    B ≤ pCore p R := by
  obtain ⟨S, hB_le_S⟩ := IsPGroup.exists_le_sylow (G := R) (p := p) hBp
  have hS_normal : (S : Subgroup R).Normal :=
    Group.IsNilpotent.sylow_normal (p := p) inferInstance S
  exact hB_le_S.trans (le_sSup ⟨hS_normal, S.isPGroup'⟩)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_commutator_le_left_of_le_normalizer
    {K A : Subgroup G}
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    ⁅K, A⁆ ≤ K := by
  let L : Subgroup G := A ⊔ K
  have hKnorm : (K.subgroupOf L).Normal := by
    simpa [L] using
      Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := A) (N := K) hAK
  haveI : (K.subgroupOf L).Normal := hKnorm
  intro x hx
  have hxmap : x ∈ (⁅K.subgroupOf L, A.subgroupOf L⁆).map L.subtype := by
    rw [commutator_subgroupOf_map_eq L A K le_sup_left le_sup_right]
    exact hx
  rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, rfl⟩
  exact (Subgroup.commutator_le_left
    (H₁ := K.subgroupOf L) (H₂ := A.subgroupOf L)) hy

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_commutator_le_right_of_normal_subgroupOf
    {M N K A : Subgroup G}
    (hNle : N ≤ M) (hKle : K ≤ M) (hAle : A ≤ N)
    [hNnorm : (N.subgroupOf M).Normal] :
    ⁅K, A⁆ ≤ N := by
  intro x hx
  have hA_le_M : A ≤ M := hAle.trans hNle
  have hxmap : x ∈ (⁅K.subgroupOf M, A.subgroupOf M⁆).map M.subtype := by
    rw [commutator_subgroupOf_map_eq M A K hA_le_M hKle]
    exact hx
  rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, rfl⟩
  have hyN : y ∈ N.subgroupOf M := by
    have hAle_sub : A.subgroupOf M ≤ N.subgroupOf M := by
      intro z hz
      exact hAle hz
    exact (Subgroup.commutator_mono (le_refl (K.subgroupOf M)) hAle_sub
      |>.trans (Subgroup.commutator_le_right
        (H₁ := K.subgroupOf M) (H₂ := N.subgroupOf M))) hy
  exact hyN

omit [IsMinCE G] in
private theorem CFSG.section12_subgroup_le_pPrimeCore_of_hasNormalPComplement_of_not_dvd
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {B : Subgroup H} (hcomp : HasNormalPComplement p H)
    (hpB : ¬ p ∣ Nat.card B) :
    B ≤ pPrimeCore p H := by
  classical
  let q : H →* H ⧸ pPrimeCore p H := QuotientGroup.mk' (pPrimeCore p H)
  have hquotp : IsPGroup p (H ⧸ pPrimeCore p H) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p) (H := H) hcomp
  have hBmap_bot : B.map q = ⊥ := by
    by_contra hne
    have hcard_ne_one : Nat.card (B.map q) ≠ 1 := by
      intro hcard
      exact hne ((Subgroup.card_eq_one (H := B.map q)).mp hcard)
    have hBmap_p : IsPGroup p (B.map q) :=
      hquotp.to_subgroup (B.map q)
    obtain ⟨n, hcard⟩ := hBmap_p.exists_card_eq
    have hp_dvd_map : p ∣ Nat.card (B.map q) := by
      cases n with
      | zero =>
          exfalso
          exact hcard_ne_one (by simpa [hcard])
      | succ n =>
          refine ⟨p ^ n, ?_⟩
          calc
            Nat.card (B.map q) = p ^ (n + 1) := hcard
            _ = p ^ n * p := by rw [pow_succ]
            _ = p * p ^ n := Nat.mul_comm _ _
    exact hpB (hp_dvd_map.trans (Subgroup.card_map_dvd (H := B) q))
  have hB_le_ker : B ≤ q.ker :=
    (Subgroup.map_eq_bot_iff (H := B) (f := q)).mp hBmap_bot
  have hker_eq : q.ker = pPrimeCore p H := by
    simp [q]
  rwa [hker_eq] at hB_le_ker

omit [IsMinCE G] in
private theorem CFSG.section12_isNilpotent_of_hasNormalPComplements
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
      haveI : Fact q.val.val.Prime := ⟨q.val.property⟩
      have hq_not_dvd_P : ¬ q.val.val ∣ Nat.card (P : Subgroup H) := by
        intro hq_dvd
        rcases P.isPGroup'.exists_card_eq with ⟨n, hcardP⟩
        have hq_dvd_pow : q.val.val ∣ p ^ n := by
          simpa [hcardP] using hq_dvd
        have hq_eq_p : q.val.val = p :=
          Nat.prime_eq_prime_of_dvd_pow q.val.property hp.out hq_dvd_pow
        exact q.property.2 hq_eq_p
      exact section12_subgroup_le_pPrimeCore_of_hasNormalPComplement_of_not_dvd
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
        haveI : Fact q.Prime := ⟨hqprime⟩
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

omit [IsMinCE G] in
private theorem CFSG.section12_hasNormalPComplement_quotient_of_le_pPrimeCore
    {H : Type*} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    {p : ℕ} [Fact p.Prime]
    (hN_le_core : N ≤ pPrimeCore p H) (hcomp : HasNormalPComplement p H) :
    HasNormalPComplement p (H ⧸ N) := by
  classical
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  let C : Subgroup (H ⧸ N) := (pPrimeCore p H).map q
  have hCnormal : C.Normal :=
    Subgroup.Normal.map (H := pPrimeCore p H) (inferInstance : (pPrimeCore p H).Normal) q
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

private theorem CFSG.section12_mbetaSubgroup_le_msigmaSubgroup
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    section10MbetaSubgroup M ≤ section10MsigmaSubgroup M := by
  have hβsub_sigma : IsPiSubgroup (G := M) (section10SigmaPrimes M)
      (section10MbetaSubgroup M) := by
    intro r hr
    have hrβ : r ∈ section10BetaPrimes M :=
      (lemma_10_8_a (G := G) hM).2.p_in_pi_of_p_dvd_card r hr
    exact section12_sigmaPrimes_mem_of_alphaPrimes_mem hM hrβ.1
  simpa [section10MsigmaSubgroup] using
    (le_piCore_of_normal_isPiSubgroup (G := M) (section10SigmaPrimes M)
      (section10MbetaSubgroup M) hβsub_sigma)

private theorem CFSG.section12_derived_quotient_mbeta_hasNormalPComplement
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hp_dvd :
      p.val ∣ Nat.card
        (derivedSubgroup M ⧸ (section10MbetaSubgroup M).subgroupOf (derivedSubgroup M))) :
    HasNormalPComplement p.val
      (derivedSubgroup M ⧸ (section10MbetaSubgroup M).subgroupOf (derivedSubgroup M)) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  let N : Subgroup M := section10MbetaSubgroup M
  let D : Subgroup M := derivedSubgroup M
  have hNleD : N ≤ D := by
    exact (section12_mbetaSubgroup_le_msigmaSubgroup (G := G) hM).trans
      (theorem_10_2_c (G := G) hM).2
  let Nsub : Subgroup D := N.subgroupOf D
  have hNHall : IsHallSubgroup (section10BetaPrimes M) N :=
    (lemma_10_8_a (G := G) hM).2
  have hp_dvd_D : p.val ∣ Nat.card D :=
    hp_dvd.trans (Subgroup.card_quotient_dvd_card (s := Nsub))
  have hpM : p ∈ subgroupPrimeSet M := by
    exact hp_dvd_D.trans (Subgroup.card_subgroup_dvd_card D)
  have hp_dvd_Nidx : p.val ∣ N.index := by
    have hp_dvd_Nsubidx : p.val ∣ Nsub.index := by
      rw [Subgroup.index_eq_card]
      change p.val ∣ Nat.card
        (derivedSubgroup M ⧸ (section10MbetaSubgroup M).subgroupOf (derivedSubgroup M))
      exact hp_dvd
    have hmap : Nsub.map D.subtype = N := by
      ext x
      simp [Nsub, N, hNleD]
    have hidx : N.index = Nsub.index * D.index := by
      have h := Subgroup.index_map_subtype (H := D) (K := Nsub)
      simpa [hmap] using h
    exact hp_dvd_Nsubidx.trans ⟨D.index, hidx⟩
  have hpβ : p ∉ section10BetaPrimes M :=
    hNHall.p_in_pi_of_p_dvd_index p hp_dvd_Nidx
  have hcompD : HasNormalPComplement p.val D :=
    (lemma_10_8_c (G := G) hM hpM hpβ).1
  have hp_not_dvd_Nsub : ¬ p.val ∣ Nat.card Nsub := by
    intro hpNsub
    have hcard : Nat.card Nsub = Nat.card N := by
      simpa [Nsub, N] using
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := N) (K := D) hNleD).toEquiv
    have hpN : p.val ∣ Nat.card N := by
      simpa [hcard] using hpNsub
    exact hpβ (hNHall.p_in_pi_of_p_dvd_card p hpN)
  have hNsub_le_core : Nsub ≤ pPrimeCore p.val D :=
    section12_subgroup_le_pPrimeCore_of_hasNormalPComplement_of_not_dvd
      (H := D) (p := p.val) (B := Nsub) hcompD hp_not_dvd_Nsub
  exact section12_hasNormalPComplement_quotient_of_le_pPrimeCore
    (H := D) (N := Nsub) (p := p.val) hNsub_le_core hcompD

private theorem CFSG.section12_derived_quotient_mbeta_nilpotent
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    Group.IsNilpotent
      (derivedSubgroup M ⧸ (section10MbetaSubgroup M).subgroupOf (derivedSubgroup M)) := by
  classical
  exact section12_isNilpotent_of_hasNormalPComplements
    (H := derivedSubgroup M ⧸
      (section10MbetaSubgroup M).subgroupOf (derivedSubgroup M))
    (fun r hr =>
      section12_derived_quotient_mbeta_hasNormalPComplement
        (G := G) hM hr)

omit [IsMinCE G] in
public theorem CFSG.section12_sylow_inf_normal_ne_bot_of_prime_dvd_normal
    {R : Type*} [Group R] [Finite R] {D : Subgroup R} [D.Normal]
    {p : Nat.Primes} (S : Sylow p.val R)
    (hpD : p ∈ subgroupPrimeSet D) :
    (S : Subgroup R) ⊓ D ≠ ⊥ := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let QD : Sylow p.val D := Classical.choice (Sylow.nonempty (p := p.val) (G := D))
  have hQD_ne_bot : (QD : Subgroup D) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := D) QD hpD
  let Qmap : Subgroup R := (QD : Subgroup D).map D.subtype
  have hQmap_ne_bot : Qmap ≠ ⊥ := by
    intro hQmap_bot
    have hQD_bot : (QD : Subgroup D) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := (QD : Subgroup D)) (f := D.subtype)
        D.subtype_injective).1 (by simpa [Qmap] using hQmap_bot)
    exact hQD_ne_bot hQD_bot
  have hQmap_p : IsPGroup p.val Qmap := IsPGroup.map QD.isPGroup' D.subtype
  obtain ⟨T, hQT⟩ := IsPGroup.exists_le_sylow (G := R) (p := p.val) hQmap_p
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R T S
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hQmap_ne_bot with ⟨q, hq_ne⟩
  let x : R := g * (q : R) * g⁻¹
  have hqD : (q : R) ∈ D := by
    rcases q.property with ⟨d, _hd, hdq⟩
    have hqd : (q : R) = d := hdq.symm
    simp [hqd]
  have hxS : x ∈ (S : Subgroup R) := by
    have hxConjT : x ∈ MulAut.conj g • (T : Subgroup R) := by
      simpa [x, MulAut.conj_apply] using
        (Subgroup.smul_mem_pointwise_smul (q : R) (MulAut.conj g) (T : Subgroup R)
          (hQT q.property))
    have hxSyl : x ∈ ((g • T : Sylow p.val R) : Subgroup R) := by
      simpa [Sylow.coe_subgroup_smul] using hxConjT
    simpa [hg] using hxSyl
  have hxD : x ∈ D := by
    simpa [x] using
      Subgroup.Normal.conj_mem (inferInstance : D.Normal) (q : R) hqD g
  have hx_ne : x ≠ 1 := by
    intro hx
    have hq_eq : (q : R) = 1 := by
      calc
        (q : R) = g⁻¹ * x * g := by simp [x, mul_assoc]
        _ = 1 := by simp [hx]
    exact hq_ne (Subtype.ext hq_eq)
  exact Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨x, hxS, hxD⟩, by
    exact fun hxbot => hx_ne (congrArg Subtype.val hxbot)⟩

private theorem CFSG.section12_sylow_le_derived_of_sigma_or_tau3
    {M : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hq : q ∈ section10SigmaPrimes M ∨ q ∈ section12Tau3Primes M)
    (S : Sylow q.val M) :
    (S : Subgroup M) ≤ derivedSubgroup M := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  rcases hq with hqσ | hqτ3
  · exact section10_sigma_sylow_le_derivedSubgroup (G := G) hM hqσ S
  · rcases (by simpa [section12Tau3Primes] using hqτ3) with
      ⟨_hqσ, hqD, hrank⟩
    have hqM : q.val ∣ Nat.card M :=
      hqD.trans (Subgroup.card_subgroup_dvd_card (derivedSubgroup M))
    have hqG : q.val ∣ Nat.card G :=
      hqM.trans (Subgroup.card_subgroup_dvd_card M)
    have hqodd : q.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hqG
    have hcyc : IsCyclic (S : Subgroup M) :=
      section10_sylow_isCyclic_of_primeRank_le_one
        (G := G) S hqodd (by omega)
    rcases corollary_1_19_a (G := M) q.val S hcyc with hbot | hle
    · exfalso
      exact section12_sylow_inf_normal_ne_bot_of_prime_dvd_normal
        (R := M) (D := derivedSubgroup M) S hqD hbot
    · exact hle

private theorem CFSG.section12_sigma_or_tau3_of_not_tau12
    {M : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hqM : q ∈ subgroupPrimeSet M)
    (hqτ1 : q ∉ section12Tau1Primes M)
    (hqτ2 : q ∉ section12Tau2Primes M) :
    q ∈ section10SigmaPrimes M ∨ q ∈ section12Tau3Primes M := by
  classical
  by_cases hqσ : q ∈ section10SigmaPrimes M
  · exact Or.inl hqσ
  · right
    have hpos : 1 ≤ primeRank q.val M :=
      section12_primeRank_pos_of_mem_subgroupPrimeSet (R := M) hqM
    have hle_two : primeRank q.val M ≤ 2 := by
      by_contra hnot
      have hgt : 2 < primeRank q.val M := by omega
      exact hqσ (section12_sigmaPrimes_mem_of_alphaPrimes_mem hM ⟨hqM, hgt⟩)
    have hrank : primeRank q.val M = 1 ∨ primeRank q.val M = 2 := by omega
    rcases hrank with hrank1 | hrank2
    · by_cases hqD : q ∈ subgroupPrimeSet (derivedSubgroup M)
      · simpa [section12Tau3Primes] using ⟨hqσ, hqD, hrank1⟩
      · exfalso
        exact hqτ1 (by simpa [section12Tau1Primes] using ⟨hqσ, hqD, hrank1⟩)
    · exfalso
      exact hqτ2 (by simpa [section12Tau2Primes] using ⟨hqσ, hrank2⟩)

/-- Lemma 12.11(b). -/
public theorem CFSG.lemma_12_11_b
    {M E E₁₂ E₁ E₂ E₃ A Mstar : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A : Set G))) :
    section12QuotientPrimeSet (subgroupCentralizerIn E A) E ⊆
      section12Tau1Primes Mstar ∪ section12Tau2Primes Mstar := by
  classical
  have hAnormE : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).1
  have hE_norm_A : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAnormE.1).1 hAnormE.2
  have hE_le_Mstar : E ≤ Mstar := hE_norm_A.trans hMstar.2
  have hA_Mstar : A ∈ section12RankTwoElementaryAbelianIn p Mstar :=
    section12_rankTwo_mono hA hE_le_Mstar
  have hp_data :=
    (lemma_12_11_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (Mstar := Mstar)
      (p := p) hM hE hp hA hMstar) hp
  have hpσstar : p ∈ section10SigmaPrimes Mstar := hp_data.1
  have hp_not_beta_star : p ∉ section10BetaPrimes Mstar := hp_data.2
  have hA_le_Mstar : A ≤ Mstar := section12_rankTwo_le hA_Mstar
  have hA_le_sigma_star : A ≤ section10Msigma Mstar :=
    section12_rankTwo_le_msigma_of_sigma
      (G := G) (M := Mstar) (A := A) (p := p) hMstar.1 hpσstar hA_Mstar
  have hAp : IsPGroup p.val A := by
    have hElem := (section12_rankTwo_elementary hA).2
    haveI : IsElementaryAbelian p.val A := hElem
    exact IsElementaryAbelian.isPGroup p.val A
  intro q hqQuot
  by_cases hqτstar : q ∈ section12Tau1Primes Mstar ∪ section12Tau2Primes Mstar
  · exact hqτstar
  · rcases hqQuot with ⟨hCE, hqidx⟩
    have hqτ1 : q ∈ section12Tau1Primes M :=
      (corollary_12_10_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA).2.2 ⟨hCE, hqidx⟩
    have hqp : q ≠ p := by
      intro hqp
      have hqrank : primeRank q.val M = 1 := by
        simpa [hqp] using hqτ1.2.2
      have hprank : primeRank q.val M = 2 := by
        simpa [hqp] using hp.2
      omega
    have hqE : q ∈ subgroupPrimeSet E := by
      have hcardE :
          ((subgroupCentralizerIn E A).subgroupOf E).index *
              Nat.card ((subgroupCentralizerIn E A).subgroupOf E) =
            Nat.card E :=
        Subgroup.index_mul_card (H := (subgroupCentralizerIn E A).subgroupOf E)
      have hq_card_E : q.val ∣ Nat.card E := by
        rw [← hcardE]
        exact dvd_mul_of_dvd_left hqidx _
      simpa [subgroupPrimeSet] using hq_card_E
    haveI : Fact q.val.Prime := ⟨q.2⟩
    have hqMstar : q ∈ subgroupPrimeSet Mstar :=
      section8_subgroupPrimeSet_mono hE_le_Mstar hqE
    let Q : Sylow q.val E := Classical.choice (Sylow.nonempty (p := q.val) (G := E))
    let QG : Subgroup G := section10AmbientSylowSubgroup E Q
    have hQG_le_E : QG ≤ E := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hQG_le_Mstar : QG ≤ Mstar := hQG_le_E.trans hE_le_Mstar
    have hQG_q : IsPGroup q.val QG := by
      change IsPGroup q.val ((Q : Subgroup E).map E.subtype)
      exact IsPGroup.map Q.isPGroup' E.subtype
    let QsubMstar : Subgroup Mstar := QG.subgroupOf Mstar
    have hQsub_q : IsPGroup q.val QsubMstar := by
      exact hQG_q.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := QG) (K := Mstar) hQG_le_Mstar).symm
    obtain ⟨S, hQsub_le_S⟩ := IsPGroup.exists_le_sylow (G := Mstar) (p := q.val) hQsub_q
    have hqστ3 :
        q ∈ section10SigmaPrimes Mstar ∨ q ∈ section12Tau3Primes Mstar :=
      section12_sigma_or_tau3_of_not_tau12
        (G := G) (M := Mstar) (q := q) hMstar.1 hqMstar
        (fun h => hqτstar (Or.inl h)) (fun h => hqτstar (Or.inr h))
    have hS_le_D : (S : Subgroup Mstar) ≤ derivedSubgroup Mstar :=
      section12_sylow_le_derived_of_sigma_or_tau3
        (G := G) (M := Mstar) (q := q) hMstar.1 hqστ3 S
    let CsubE : Subgroup E := (subgroupCentralizerIn E A).subgroupOf E
    have hCnormE : section10NormalIn (subgroupCentralizerIn E A) E :=
      section12_subgroupCentralizerIn_normal_of_normal (G := G) (E := E) (A := A) hAnormE
    haveI : CsubE.Normal := by
      simpa [CsubE] using hCnormE.2
    let qE : E →* E ⧸ CsubE := QuotientGroup.mk' CsubE
    let QbarE : Sylow q.val (E ⧸ CsubE) :=
      Q.mapSurjective (f := qE) (QuotientGroup.mk'_surjective CsubE)
    have hQmap_ne_bot : ((Q : Subgroup E).map qE) ≠ ⊥ := by
      have hQbar_ne_bot : (QbarE : Subgroup (E ⧸ CsubE)) ≠ ⊥ :=
        Sylow.ne_bot_of_dvd_card (G := E ⧸ CsubE) QbarE
          (by simpa [CsubE, Subgroup.index_eq_card] using hqidx)
      simpa [QbarE, qE]
        using hQbar_ne_bot
    let C : Subgroup G := ⁅A, QG⁆
    have hC_le_A : C ≤ A := by
      have hQ_norm_A : QG ≤ Subgroup.normalizer (A : Set G) :=
        hQG_le_E.trans hE_norm_A
      simpa [C] using
        section12_commutator_le_left_of_le_normalizer
          (G := G) (K := A) (A := QG) hQ_norm_A
    have hC_ne_bot : C ≠ ⊥ := by
      intro hCbot
      have hQG_le_cent : QG ≤ subgroupCentralizerIn E A := by
        have hcomm_bot : ⁅QG, A⁆ = ⊥ := by
          simpa [C, Subgroup.commutator_comm] using hCbot
        have hQG_cent_A : QG ≤ Subgroup.centralizer (A : Set G) := by
          exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := QG) (H₂ := A)).mp
            hcomm_bot
        intro x hxQ
        exact ⟨hQG_le_E hxQ, hQG_cent_A hxQ⟩
      have hQ_le_Csub : (Q : Subgroup E) ≤ CsubE := by
        intro x hxQ
        have hxQG : ((x : E) : G) ∈ QG := by
          exact Subgroup.mem_map.mpr ⟨x, hxQ, rfl⟩
        have hxC : ((x : E) : G) ∈ subgroupCentralizerIn E A := hQG_le_cent hxQG
        simpa [CsubE, Subgroup.mem_subgroupOf] using hxC
      have hQmap_bot : (Q : Subgroup E).map qE = ⊥ := by
        exact (Subgroup.map_eq_bot_iff (H := (Q : Subgroup E)) (f := qE)).2 <|
          by simpa [qE, QuotientGroup.ker_mk'] using hQ_le_Csub
      exact hQmap_ne_bot hQmap_bot
    let α : Subgroup Mstar := section10MbetaSubgroup Mstar
    let D : Subgroup Mstar := derivedSubgroup Mstar
    have hA_sub_sigma : A.subgroupOf Mstar ≤ section10MsigmaSubgroup Mstar := by
      intro x hx
      have hxA : ((x : Mstar) : G) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using hx
      have hxσ : ((x : Mstar) : G) ∈ section10Msigma Mstar := hA_le_sigma_star hxA
      have hxσsub : x ∈ (section10Msigma Mstar).subgroupOf Mstar := by
        simpa [Subgroup.mem_subgroupOf] using hxσ
      have hσeq :
          (section10Msigma Mstar).subgroupOf Mstar = section10MsigmaSubgroup Mstar := by
        simpa [section10Msigma] using
          (subgroupOf_map_subtype_eq (K := Mstar) (H := section10MsigmaSubgroup Mstar))
      rw [hσeq] at hxσsub
      exact hxσsub
    have hA_sub_D : A.subgroupOf Mstar ≤ D :=
      hA_sub_sigma.trans (by simpa [D] using (theorem_10_2_c (G := G) hMstar.1).2)
    have hα_le_D : α ≤ D := by
      exact (section12_mbetaSubgroup_le_msigmaSubgroup (G := G) hMstar.1).trans
        (theorem_10_2_c (G := G) hMstar.1).2
    haveI : α.Normal := by
      dsimp [α]
      infer_instance
    haveI : (α.subgroupOf D).Normal := by
      simpa [α, D] using
        (Subgroup.Normal.subgroupOf (inferInstance : α.Normal) D)
    let qMstar : Mstar →* Mstar ⧸ α := QuotientGroup.mk' α
    let Dbar : Subgroup (Mstar ⧸ α) := D.map qMstar
    have hDbar_norm : Dbar.Normal := by
      dsimp [Dbar]
      exact Subgroup.Normal.map (H := D) inferInstance qMstar
        (QuotientGroup.mk'_surjective α)
    haveI : Dbar.Normal := hDbar_norm
    have hDquot_nil :
        Group.IsNilpotent (D ⧸ α.subgroupOf D) :=
      section12_derived_quotient_mbeta_nilpotent
        (G := G) (M := Mstar) hMstar.1
    have hDbar_nil : Group.IsNilpotent Dbar := by
      let e : D ⧸ α.subgroupOf D ≃* Dbar := quotientSubgroupRangeEquiv D α
      exact Group.nilpotent_of_mulEquiv (G := D ⧸ α.subgroupOf D) (G' := Dbar) e
    let QbarM : Subgroup (Mstar ⧸ α) := QsubMstar.map qMstar
    have hQbar_le_Dbar : QbarM ≤ Dbar := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hxQ, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x, hS_le_D (hQsub_le_S hxQ), rfl⟩
    let QbarD : Subgroup Dbar := QbarM.subgroupOf Dbar
    have hQbarD_q : IsPGroup q.val QbarD := by
      let e : QbarD ≃* QbarM := Subgroup.subgroupOfEquivOfLe hQbar_le_Dbar
      exact (IsPGroup.map hQsub_q qMstar).of_equiv e.symm
    let PbarSub : Subgroup Dbar := pCore q.val Dbar
    have hPbarSub_char : PbarSub.Characteristic := by
      dsimp [PbarSub]
      exact section12_pCore_characteristic (R := Dbar) (p := q.val)
    haveI : PbarSub.Characteristic := hPbarSub_char
    have hQbarD_le_pcore : QbarD ≤ PbarSub := by
      haveI : Group.IsNilpotent Dbar := hDbar_nil
      simpa [PbarSub] using
        section12_pSubgroup_le_pCore_of_nilpotent
          (R := Dbar) (p := q.val) (B := QbarD) hQbarD_q
    let Pbar : Subgroup (Mstar ⧸ α) := PbarSub.map Dbar.subtype
    have hPbar_norm : Pbar.Normal := by
      dsimp [Pbar]
      infer_instance
    let Nsub : Subgroup Mstar := Pbar.comap qMstar
    have hNsub_norm : Nsub.Normal := by
      dsimp [Nsub]
      exact hPbar_norm.comap qMstar
    let N : Subgroup G := Nsub.map Mstar.subtype
    have hNle : N ≤ Mstar := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hNsub_eq : N.subgroupOf Mstar = Nsub := by
      simpa [N] using subgroupOf_map_subtype_eq (K := Mstar) Nsub
    have hNnorm : (N.subgroupOf Mstar).Normal := by
      rw [hNsub_eq]
      exact hNsub_norm
    have hQG_le_N : QG ≤ N := by
      intro x hxQ
      refine Subgroup.mem_map.mpr ?_
      refine ⟨⟨x, hQG_le_Mstar hxQ⟩, ?_, rfl⟩
      change qMstar ⟨x, hQG_le_Mstar hxQ⟩ ∈ Pbar
      have hxQbar : qMstar ⟨x, hQG_le_Mstar hxQ⟩ ∈ QbarM := by
        exact Subgroup.mem_map.mpr
          ⟨⟨x, hQG_le_Mstar hxQ⟩, by
            simpa [QsubMstar, Subgroup.mem_subgroupOf] using hxQ, rfl⟩
      have hxDbar : qMstar ⟨x, hQG_le_Mstar hxQ⟩ ∈ Dbar :=
        hQbar_le_Dbar hxQbar
      have hxQbarD :
          (⟨qMstar ⟨x, hQG_le_Mstar hxQ⟩, hxDbar⟩ : Dbar) ∈ QbarD := by
        simpa [QbarD, Subgroup.mem_subgroupOf] using hxQbar
      have hxpcore : (⟨qMstar ⟨x, hQG_le_Mstar hxQ⟩, hxDbar⟩ : Dbar) ∈ PbarSub :=
        hQbarD_le_pcore hxQbarD
      exact Subgroup.mem_map.mpr
        ⟨⟨qMstar ⟨x, hQG_le_Mstar hxQ⟩, hxDbar⟩, hxpcore, rfl⟩
    have hC_le_Mstar : C ≤ Mstar := hC_le_A.trans hA_le_Mstar
    have hC_le_N : C ≤ N := by
      haveI : (N.subgroupOf Mstar).Normal := hNnorm
      simpa [C] using
        section12_commutator_le_right_of_normal_subgroupOf
          (G := G) (M := Mstar) (N := N) (K := A) (A := QG)
          hNle hA_le_Mstar hQG_le_N
    have hCp : IsPGroup p.val C := by
      let CsubA : Subgroup A := C.subgroupOf A
      have hCsubA_p : IsPGroup p.val CsubA := hAp.to_subgroup CsubA
      exact hCsubA_p.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := C) (K := A) hC_le_A)
    have hC_pi' : IsPiSubgroup (G := G) (section10PPrimeSet q) C := by
      have hC_pi : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) C :=
        section8_isPiSubgroup_singleton_of_isPGroup hCp
      intro r hr
      have hr_single : r ∈ ({p} : Set Nat.Primes) := hC_pi r hr
      have hrp : r = p := by simpa using hr_single
      rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hrq
      exact hqp (hrq.symm.trans hrp)
    let Cbar : Subgroup (Mstar ⧸ α) := (C.subgroupOf Mstar).map qMstar
    have hCsub_pi' : IsPiSubgroup (G := Mstar) (section10PPrimeSet q) (C.subgroupOf Mstar) :=
      section12_isPiSubgroup_subgroupOf hC_pi' hC_le_Mstar
    have hCbar_pi' : IsPiSubgroup (G := Mstar ⧸ α) (section10PPrimeSet q) Cbar := by
      simpa [Cbar] using section12_isPiSubgroup_map hCsub_pi' qMstar
    have hPbar_q : IsPiSubgroup (G := Mstar ⧸ α) ({q} : Set Nat.Primes) Pbar := by
      have hPbar_qgroup : IsPGroup q.val Pbar := by
        dsimp [Pbar, PbarSub]
        exact IsPGroup.map (pCore_isPGroup (G := Dbar) (p := q.val)) Dbar.subtype
      exact section8_isPiSubgroup_singleton_of_isPGroup hPbar_qgroup
    have hCbar_le_Pbar : Cbar ≤ Pbar := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hxC, rfl⟩
      have hxCG : ((x : Mstar) : G) ∈ C := by
        simpa [Subgroup.mem_subgroupOf] using hxC
      have hxN : ((x : Mstar) : G) ∈ N := hC_le_N hxCG
      rcases Subgroup.mem_map.mp hxN with ⟨z, hzN, hzx⟩
      have hz_eq : z = x := Mstar.subtype_injective hzx
      have hxNsub : x ∈ Nsub := by
        simpa [hz_eq] using hzN
      exact hxNsub
    have hCbar_q : IsPiSubgroup (G := Mstar ⧸ α) ({q} : Set Nat.Primes) Cbar :=
      IsPiSubgroup.of_le hCbar_le_Pbar hPbar_q
    have hCbar_bot : Cbar = ⊥ := by
      exact section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
        (π := ({q} : Set Nat.Primes)) (H := Cbar) (Y := Cbar) (C := Cbar)
        le_rfl le_rfl (by simpa [section10PPrimeSet] using hCbar_pi') hCbar_q
    have hC_le_beta : C ≤ section10Mbeta Mstar := by
      intro x hxC
      let xM : Mstar := ⟨x, hC_le_Mstar hxC⟩
      have hxCsub : xM ∈ C.subgroupOf Mstar := by
        simpa [xM, Subgroup.mem_subgroupOf] using hxC
      have hxmap : qMstar xM ∈ Cbar := Subgroup.mem_map.mpr ⟨xM, hxCsub, rfl⟩
      have hxone : qMstar xM = 1 := by
        simpa [hCbar_bot] using hxmap
      have hxker : xM ∈ qMstar.ker := by
        simpa [MonoidHom.mem_ker] using hxone
      have hxα : xM ∈ α := by
        simpa [qMstar, QuotientGroup.ker_mk'] using hxker
      change x ∈ (section10MbetaSubgroup Mstar).map Mstar.subtype
      exact Subgroup.mem_map.mpr ⟨xM, by simpa [α] using hxα, rfl⟩
    haveI : Nontrivial C :=
      (Subgroup.nontrivial_iff_ne_bot (H := C)).2 hC_ne_bot
    have hp_dvd_C : p.val ∣ Nat.card C :=
      section12_prime_dvd_card_of_nontrivial_pSubgroup (G := G) (p := p) (B := C) hCp inferInstance
    have hp_dvd_beta : p.val ∣ Nat.card (section10Mbeta Mstar) :=
      hp_dvd_C.trans (Subgroup.card_dvd_of_le hC_le_beta)
    have hpβstar : p ∈ section10BetaPrimes Mstar :=
      (lemma_10_8_a (G := G) hMstar.1).1.p_in_pi_of_p_dvd_card p hp_dvd_beta
    exact False.elim (hp_not_beta_star hpβstar)

end Section12
