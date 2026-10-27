module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.lemma_11_1_b
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

/-!
# Corollary 11.2 infrastructure

This file contains the shared Section 11 support used by Corollary 11.2 and later declarations.
-/

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_map_subtype_le_normalizer_of_normal
    (K : Subgroup G) (H : Subgroup K) [H.Normal] :
    K ≤ Subgroup.normalizer (H.map K.subtype) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases hx with ⟨h, hhH, rfl⟩
    exact Subgroup.mem_map_of_mem K.subtype
      (Subgroup.Normal.conj_mem inferInstance h hhH ⟨k, hk⟩)
  · intro hx
    rcases hx with ⟨h, hhH, hhx⟩
    refine ⟨(⟨k, hk⟩ : K)⁻¹ * h * ⟨k, hk⟩, ?_, ?_⟩
    · simpa using Subgroup.Normal.conj_mem inferInstance h hhH ((⟨k, hk⟩ : K)⁻¹)
    · calc
        (((⟨k, hk⟩ : K)⁻¹ * h * ⟨k, hk⟩ : K) : G) =
            k⁻¹ * ((h : K) : G) * k := by rfl
        _ = k⁻¹ * (k * x * k⁻¹) * k := by
          have hhx' : (h : G) = k * x * k⁻¹ := hhx
          rw [hhx']
        _ = x := by simp [mul_assoc]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_msigma_le_normalizer (M : Subgroup G) :
    M ≤ Subgroup.normalizer (section10Msigma M : Set G) := by
  simpa [section10Msigma] using
    (section11_map_subtype_le_normalizer_of_normal
      (K := M) (H := section10MsigmaSubgroup M))

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_conjBy_le_normalizer_conjBy_of_le_normalizer
    {H K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G)) (g : G) :
    H.conjBy g ≤ Subgroup.normalizer (K.conjBy g : Set G) := by
  refine subgroup_le_normalizer_of_conj_mem (K.conjBy g) (H.conjBy g) ?_
  intro r x hx
  rcases Subgroup.mem_map.mp r.property with ⟨r₀, hr₀, hr_eq⟩
  rcases Subgroup.mem_map.mp hx with ⟨x₀, hx₀, hx_eq⟩
  refine Subgroup.mem_map.mpr ⟨r₀ * x₀ * r₀⁻¹, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hHK hr₀) x₀).1 hx₀
  · change g * (r₀ * x₀ * r₀⁻¹) * g⁻¹ = (r : G) * x * (r : G)⁻¹
    rw [← hr_eq, ← hx_eq]
    simp [MulAut.conj_apply]
    group

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_hall_le_of_isPiSubgroup_of_le_normalizer
    {π : Set Nat.Primes} {H K : Subgroup G}
    (hH : IsHallSubgroup π H) (hKπ : IsPiSubgroup (G := G) π K)
    (hK_norm : K ≤ Subgroup.normalizer (H : Set G)) :
    K ≤ H := by
  let HK : Subgroup G := K ⊔ H
  have hHsub_norm : (H.subgroupOf HK).Normal := by
    simpa [HK] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := K) (N := H) hK_norm)
  have hrel_dvd_cardK : H.relIndex HK ∣ Nat.card K := by
    change (H.subgroupOf HK).index ∣ Nat.card K
    have htop : H.subgroupOf HK ⊔ K.subgroupOf HK = ⊤ := by
      calc
        H.subgroupOf HK ⊔ K.subgroupOf HK = (H ⊔ K).subgroupOf HK := by
          symm
          simpa [HK] using
            (Subgroup.subgroupOf_sup (A := H) (A' := K) (B := HK)
              (by exact le_sup_right) (by exact le_sup_left))
        _ = ⊤ := by
          apply (Subgroup.subgroupOf_eq_top).2
          simp [HK, sup_comm]
    have hrel_eq :
        (H.subgroupOf HK).index =
          (H.subgroupOf HK).relIndex (K.subgroupOf HK) := by
      calc
        (H.subgroupOf HK).index = (H.subgroupOf HK).relIndex ⊤ := by
          exact (Subgroup.relIndex_top_right (H := H.subgroupOf HK)).symm
        _ = (H.subgroupOf HK).relIndex (H.subgroupOf HK ⊔ K.subgroupOf HK) := by
          rw [← htop]
        _ = (H.subgroupOf HK).relIndex (K.subgroupOf HK) := by
          rw [sup_comm]
          exact Subgroup.relIndex_sup_right (H := K.subgroupOf HK) (K := H.subgroupOf HK)
    have hdiv :
        (H.subgroupOf HK).relIndex (K.subgroupOf HK) ∣ Nat.card (K.subgroupOf HK) :=
      Subgroup.relIndex_dvd_card (H := H.subgroupOf HK) (K := K.subgroupOf HK)
    have hcard_Ksub : Nat.card (K.subgroupOf HK) = Nat.card K := by
      simpa using
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := K) (K := HK)
          (by exact le_sup_left)).toEquiv
    exact hrel_eq ▸ (hcard_Ksub ▸ hdiv)
  have hrel_dvd_index : H.relIndex HK ∣ H.index :=
    Subgroup.relIndex_dvd_index_of_le (H := H) (K := HK) le_sup_right
  have hcop : Nat.Coprime (Nat.card K) H.index := by
    refine Nat.coprime_of_dvd ?_
    intro q hqprime hq_dvd_card hq_dvd_index
    let q' : Nat.Primes := ⟨q, hqprime⟩
    have hq_mem : q' ∈ π := hKπ q' hq_dvd_card
    have hq_not_mem : q' ∉ π := hH.p_in_pi_of_p_dvd_index q' hq_dvd_index
    exact hq_not_mem hq_mem
  have hrel_eq_one : H.relIndex HK = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hrel_dvd_cardK hrel_dvd_index
  have hHK_le_H : HK ≤ H := (Subgroup.relIndex_eq_one).1 hrel_eq_one
  exact le_trans le_sup_left hHK_le_H

omit [IsMinCE G] in
private theorem CFSG.section11_A_isPGroup
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    IsPGroup p.val A := by
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases h11.A_rank_two with ⟨_hAcard, hAelem⟩
  letI : IsElementaryAbelian p.val A := hAelem
  exact IsElementaryAbelian.isPGroup p.val A

omit [IsMinCE G] in
public theorem CFSG.section11_coprime_A_of_isPiSubgroup_sigma
    {M A0 A H : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P)
    (hHσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) H) :
    Nat.Coprime (Nat.card A) (Nat.card H) := by
  have hHp' : IsPiSubgroup (G := G) ({p} : Set Nat.Primes)ᶜ H := by
    intro r hrH hrp
    have hrσ : r ∈ section10SigmaPrimes M := hHσ r hrH
    have hr_eq_p : r = p := by simpa using hrp
    exact h11.not_sigma (by simpa [hr_eq_p] using hrσ)
  exact section8_coprime_card_of_isPGroup_of_isPiSubgroup_compl
    (π := ({p} : Set Nat.Primes)) (r := p) (R := A) (Y := H) (by simp)
    (section11_A_isPGroup h11) hHp'

public theorem CFSG.section11_solvable_of_le_maximal
    {M H : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) (hHM : H ≤ M) :
    IsSolvable H := by
  have hHproper : H ≠ ⊤ := by
    intro hHtop
    exact hM.1 (top_unique (by simpa [hHtop] using hHM))
  exact IsMinCE.proper_subgroups_solvable H (lt_top_iff_ne_top.mpr hHproper)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_le_normalizer_map_of_isInvariant
    {A H : Subgroup G} {K : Subgroup H}
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) :
    haveI : Subgroup.Normalizes A H := ⟨hAH⟩
    IsInvariant (↥A) (↥H) K →
    A ≤ Subgroup.normalizer (K.map H.subtype : Set G) := by
  intro hKinv
  haveI : Subgroup.Normalizes A H := ⟨hAH⟩
  letI : IsInvariant (↥A) (↥H) K := hKinv
  refine subgroup_le_normalizer_of_conj_mem (K.map H.subtype) A ?_
  intro a x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  have hyInv : a • y ∈ K :=
    (IsInvariant.invariant (A := ↥A) (G := ↥H) (H := K) a y).1 hy
  exact Subgroup.mem_map.mpr ⟨a • y, hyInv, by
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]⟩

end Section11

/-!
# Corollary 11.2(a)

This file contains the Section 11 Corollary 11.2(a) statement and proof.
-/

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]


private theorem CFSG.section11_msigma_inf_conjBy_eq
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) (g : G) :
    section10Msigma M ⊓ M.conjBy g =
      section10Msigma M ⊓ (section10Msigma M).conjBy g := by
  let K : Subgroup G := section10Msigma M
  have hKπ : IsPiSubgroup (G := G) (section10SigmaPrimes M) K :=
    (theorem_10_2_b hM).1.p_in_pi_of_p_dvd_card
  have hHallKg : IsHallSubgroup (section10SigmaPrimes M) (K.conjBy g) := by
    simpa [K, Subgroup.conjBy] using (theorem_10_2_b hM).1.map_conj g
  have hMg_norm_Kg : M.conjBy g ≤ Subgroup.normalizer (K.conjBy g : Set G) := by
    simpa [K] using
      section11_conjBy_le_normalizer_conjBy_of_le_normalizer
        (section11_msigma_le_normalizer M) g
  apply le_antisymm
  · intro x hx
    have hLπ : IsPiSubgroup (G := G) (section10SigmaPrimes M) (K ⊓ M.conjBy g) :=
      IsPiSubgroup.of_le inf_le_left hKπ
    have hL_norm : K ⊓ M.conjBy g ≤ Subgroup.normalizer (K.conjBy g : Set G) :=
      inf_le_right.trans hMg_norm_Kg
    exact ⟨hx.1, section11_hall_le_of_isPiSubgroup_of_le_normalizer hHallKg hLπ hL_norm hx⟩
  · intro x hx
    exact ⟨hx.1, (Subgroup.map_mono (section11_msigma_le M)) hx.2⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_isPiSubgroup_subgroupOf
    {π : Set Nat.Primes} {H K : Subgroup G}
    (hKπ : IsPiSubgroup (G := G) π K) (hKH : K ≤ H) :
    IsPiSubgroup (G := H) π (K.subgroupOf H) := by
  intro p hp
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  exact hKπ p (by rwa [hcard] at hp)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_isInvariant_subgroupOf_of_le_normalizer
    {A H K : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (_hKH : K ≤ H) :
    haveI : Subgroup.Normalizes A H := ⟨hAH⟩
    IsInvariant (↥A) (↥H) (K.subgroupOf H) := by
  haveI : Subgroup.Normalizes A H := ⟨hAH⟩
  refine ⟨?_⟩
  intro a x
  change ((x : H) : G) ∈ K ↔ ((a : G) * ((x : H) : G) * (a : G)⁻¹) ∈ K
  exact Subgroup.mem_normalizer_iff.mp (hAK a.property) ((x : H) : G)

private theorem CFSG.section11_sylow_of_hall_singleton
    {H : Type*} [Group H] [Finite H] {q : Nat.Primes} (R : Subgroup H)
    (hRHall : IsHallSubgroup ({q} : Set Nat.Primes) R) :
    ∃ Q : Sylow q.val H, (Q : Subgroup H) = R := by
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hRπ : IsPiSubgroup (G := H) ({q} : Set Nat.Primes) R :=
    hRHall.p_in_pi_of_p_dvd_card
  have hRp : IsPGroup q.val R :=
    section8_isPGroup_of_isPiSubgroup_singleton hRπ
  have hnot : ¬ q.val ∣ R.index := by
    intro hidx
    exact (hRHall.p_in_pi_of_p_dvd_index q hidx) (by simp)
  exact ⟨IsPGroup.toSylow (p := q.val) hRp hnot, by
    simp [IsPGroup.toSylow_coe]⟩

private theorem CFSG.section11_prime_dvd_hall_singleton_card_of_dvd_card
    {H : Type*} [Group H] [Finite H] {q : Nat.Primes} {R : Subgroup H}
    (hRHall : IsHallSubgroup ({q} : Set Nat.Primes) R)
    (hqH : q.val ∣ Nat.card H) :
    q.val ∣ Nat.card R := by
  have hprod : q.val ∣ R.index * Nat.card R := by
    simpa [Subgroup.index_mul_card (H := R)] using hqH
  rcases q.property.dvd_mul.mp hprod with hqidx | hqcard
  · exact False.elim ((hRHall.p_in_pi_of_p_dvd_index q hqidx) (by simp))
  · exact hqcard

/-- Corollary 11.2(a). -/
public theorem CFSG.corollary_11_2_a
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {g : G}
    (hgM : g ∉ M) (hAgM : A ≤ M.conjBy g) :
    section10Msigma M ⊓ M.conjBy g = ⊥ := by
  classical
  rw [section11_msigma_inf_conjBy_eq h11.maximal g]
  let K : Subgroup G := section10Msigma M
  let Kg : Subgroup G := K.conjBy g
  change K ⊓ Kg = ⊥
  by_contra hJ_ne_bot_raw
  let J : Subgroup G := K ⊓ Kg
  have hJ_ne_bot : J ≠ ⊥ := by
    simpa [J] using hJ_ne_bot_raw
  have hK_le_M : K ≤ M := by
    simpa [K] using section11_msigma_le M
  have hKg_le_Mg : Kg ≤ M.conjBy g := by
    change K.map (MulAut.conj g).toMonoidHom ≤
      M.map (MulAut.conj g).toMonoidHom
    exact Subgroup.map_mono hK_le_M
  have hHallK : IsHallSubgroup (section10SigmaPrimes M) K := by
    simpa [K] using (theorem_10_2_b h11.maximal).1
  have hKσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) K :=
    hHallK.p_in_pi_of_p_dvd_card
  have hHallKg : IsHallSubgroup (section10SigmaPrimes M) Kg := by
    simpa [K, Kg, Subgroup.conjBy] using (theorem_10_2_b h11.maximal).1.map_conj g
  have hKgσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Kg :=
    hHallKg.p_in_pi_of_p_dvd_card
  have hJ_le_K : J ≤ K := by
    simp [J]
  have hJ_le_Kg : J ≤ Kg := by
    simp [J]
  have hJσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) J :=
    IsPiSubgroup.of_le hJ_le_K hKσ
  have hcardJ_ne_one : Nat.card J ≠ 1 := by
    intro hcard
    exact hJ_ne_bot ((Subgroup.card_eq_one (H := J)).1 hcard)
  obtain ⟨q0, hq0prime, hq0J⟩ := Nat.exists_prime_and_dvd hcardJ_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  have hqJ : q.val ∣ Nat.card J := by
    simpa [q] using hq0J
  have hqσ : q ∈ section10SigmaPrimes M := by
    exact hHallK.p_in_pi_of_p_dvd_card q
      (hqJ.trans (Subgroup.card_dvd_of_le hJ_le_K))
  have hA_norm_K : A ≤ Subgroup.normalizer (K : Set G) := by
    exact h11.A_le_M.trans (by simpa [K] using section11_msigma_le_normalizer M)
  have hMg_norm_Kg : M.conjBy g ≤ Subgroup.normalizer (Kg : Set G) := by
    simpa [K, Kg] using
      section11_conjBy_le_normalizer_conjBy_of_le_normalizer
        (section11_msigma_le_normalizer M) g
  have hA_norm_Kg : A ≤ Subgroup.normalizer (Kg : Set G) :=
    hAgM.trans hMg_norm_Kg
  have hA_norm_J : A ≤ Subgroup.normalizer (J : Set G) := by
    have hA_inf :
        A ≤ Subgroup.normalizer (K : Set G) ⊓ Subgroup.normalizer (Kg : Set G) := by
      intro a ha
      exact ⟨hA_norm_K ha, hA_norm_Kg ha⟩
    exact hA_inf.trans <| by
      simpa [J] using
        (Subgroup.inf_normalizer_le_normalizer_inf :
          Subgroup.normalizer (K : Set G) ⊓ Subgroup.normalizer (Kg : Set G) ≤
            Subgroup.normalizer ((K ⊓ Kg : Subgroup G) : Set G))
  haveI : Subgroup.Normalizes A K := ⟨hA_norm_K⟩
  haveI : Subgroup.Normalizes A Kg := ⟨hA_norm_Kg⟩
  haveI : Subgroup.Normalizes A J := ⟨hA_norm_J⟩
  have hsolvJ : IsSolvable J :=
    section11_solvable_of_le_maximal h11.maximal (hJ_le_K.trans hK_le_M)
  have hcopJ : Nat.Coprime (Nat.card A) (Nat.card J) :=
    section11_coprime_A_of_isPiSubgroup_sigma h11 hJσ
  have hbotπ : IsPiSubgroup (G := J) ({q} : Set Nat.Primes) (⊥ : Subgroup J) := by
    intro r hr
    exfalso
    have : r.val ∣ (1 : ℕ) := by simpa using hr
    exact r.property.not_dvd_one this
  have hbotInv : IsInvariant (↥A) (↥J) (⊥ : Subgroup J) := by
    exact isInvariant_of_characteristic (A := ↥A) (G := ↥J) (⊥ : Subgroup J)
  obtain ⟨R0sub, hR0Hall, hR0inv, _hbot_le_R0⟩ :=
    proposition_1_5_b (G := ↥J) (A := ↥A) hsolvJ hcopJ
      ({q} : Set Nat.Primes) (⊥ : Subgroup J) hbotπ hbotInv
  let R0G : Subgroup G := R0sub.map J.subtype
  have hR0G_card : Nat.card R0G = Nat.card R0sub := by
    simpa [R0G] using
      Subgroup.card_map_of_injective (K := R0sub) (f := J.subtype) J.subtype_injective
  have hqR0sub : q.val ∣ Nat.card R0sub :=
    section11_prime_dvd_hall_singleton_card_of_dvd_card hR0Hall hqJ
  have hqR0G : q.val ∣ Nat.card R0G := by
    simpa [hR0G_card] using hqR0sub
  have hR0G_ne_bot : R0G ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card R0G = 1 := by simp [hbot]
    exact q.property.not_dvd_one (by simpa [hcard] using hqR0G)
  have hR0G_le_J : R0G ≤ J := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hR0G_le_K : R0G ≤ K := hR0G_le_J.trans hJ_le_K
  have hR0G_le_Kg : R0G ≤ Kg := hR0G_le_J.trans hJ_le_Kg
  have hR0Gπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) R0G := by
    intro r hr
    exact hR0Hall.p_in_pi_of_p_dvd_card r (by simpa [hR0G_card] using hr)
  have hA_norm_R0G : A ≤ Subgroup.normalizer (R0G : Set G) := by
    simpa [R0G] using
      section11_le_normalizer_map_of_isInvariant
        (A := A) (H := J) (K := R0sub) hA_norm_J hR0inv
  have hsolvK : IsSolvable K :=
    section11_solvable_of_le_maximal h11.maximal hK_le_M
  have hcopK : Nat.Coprime (Nat.card A) (Nat.card K) :=
    section11_coprime_A_of_isPiSubgroup_sigma h11 hKσ
  have hR0Kπ :
      IsPiSubgroup (G := K) ({q} : Set Nat.Primes) (R0G.subgroupOf K) :=
    section11_isPiSubgroup_subgroupOf hR0Gπ hR0G_le_K
  have hR0Kinv : IsInvariant (↥A) (↥K) (R0G.subgroupOf K) := by
    simpa using
      section11_isInvariant_subgroupOf_of_le_normalizer
        (A := A) (H := K) (K := R0G) hA_norm_K hA_norm_R0G hR0G_le_K
  obtain ⟨R1sub, hR1Hall, hR1inv, hR0K_le_R1⟩ :=
    proposition_1_5_b (G := ↥K) (A := ↥A) hsolvK hcopK
      ({q} : Set Nat.Primes) (R0G.subgroupOf K) hR0Kπ hR0Kinv
  rcases section11_sylow_of_hall_singleton (q := q) R1sub hR1Hall with
    ⟨Q1, hQ1eq⟩
  have hA_norm_R1G :
      A ≤ Subgroup.normalizer (R1sub.map K.subtype : Set G) :=
    section11_le_normalizer_map_of_isInvariant
      (A := A) (H := K) (K := R1sub) hA_norm_K hR1inv
  have hAQ1 :
      A ≤ Subgroup.normalizer
        (section10AmbientSylowSubgroup K Q1 : Set G) := by
    simpa [section10AmbientSylowSubgroup, hQ1eq] using hA_norm_R1G
  have hR0_le_Q1 :
      R0G ≤ section10AmbientSylowSubgroup K Q1 := by
    intro x hx
    change x ∈ (Q1 : Subgroup K).map K.subtype
    have hxKsub : (⟨x, hR0G_le_K hx⟩ : K) ∈ R0G.subgroupOf K := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxR1 : (⟨x, hR0G_le_K hx⟩ : K) ∈ R1sub :=
      hR0K_le_R1 hxKsub
    have hxQ1 : (⟨x, hR0G_le_K hx⟩ : K) ∈ (Q1 : Subgroup K) := by
      simpa [hQ1eq] using hxR1
    exact Subgroup.mem_map.mpr ⟨⟨x, hR0G_le_K hx⟩, hxQ1, rfl⟩
  have hsolvKg : IsSolvable Kg :=
    section11_solvable_of_le_maximal (section11_maximal_conjBy h11.maximal g) hKg_le_Mg
  have hcopKg : Nat.Coprime (Nat.card A) (Nat.card Kg) :=
    section11_coprime_A_of_isPiSubgroup_sigma h11 hKgσ
  have hR0Kgπ :
      IsPiSubgroup (G := Kg) ({q} : Set Nat.Primes) (R0G.subgroupOf Kg) :=
    section11_isPiSubgroup_subgroupOf hR0Gπ hR0G_le_Kg
  have hR0Kginv : IsInvariant (↥A) (↥Kg) (R0G.subgroupOf Kg) := by
    simpa using
      section11_isInvariant_subgroupOf_of_le_normalizer
        (A := A) (H := Kg) (K := R0G) hA_norm_Kg hA_norm_R0G hR0G_le_Kg
  obtain ⟨R2sub, hR2Hall, hR2inv, hR0Kg_le_R2⟩ :=
    proposition_1_5_b (G := ↥Kg) (A := ↥A) hsolvKg hcopKg
      ({q} : Set Nat.Primes) (R0G.subgroupOf Kg) hR0Kgπ hR0Kginv
  rcases section11_sylow_of_hall_singleton (q := q) R2sub hR2Hall with
    ⟨Q2, hQ2eq⟩
  have hA_norm_R2G :
      A ≤ Subgroup.normalizer (R2sub.map Kg.subtype : Set G) :=
    section11_le_normalizer_map_of_isInvariant
      (A := A) (H := Kg) (K := R2sub) hA_norm_Kg hR2inv
  have hAQ2 :
      A ≤ Subgroup.normalizer
        (section10AmbientSylowSubgroup Kg Q2 : Set G) := by
    simpa [section10AmbientSylowSubgroup, hQ2eq] using hA_norm_R2G
  have hR0_le_Q2 :
      R0G ≤ section10AmbientSylowSubgroup Kg Q2 := by
    intro x hx
    change x ∈ (Q2 : Subgroup Kg).map Kg.subtype
    have hxKgsub : (⟨x, hR0G_le_Kg hx⟩ : Kg) ∈ R0G.subgroupOf Kg := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxR2 : (⟨x, hR0G_le_Kg hx⟩ : Kg) ∈ R2sub :=
      hR0Kg_le_R2 hxKgsub
    have hxQ2 : (⟨x, hR0G_le_Kg hx⟩ : Kg) ∈ (Q2 : Subgroup Kg) := by
      simpa [hQ2eq] using hxR2
    exact Subgroup.mem_map.mpr ⟨⟨x, hR0G_le_Kg hx⟩, hxQ2, rfl⟩
  have hQinf_bot :
      section10AmbientSylowSubgroup K Q1 ⊓
          section10AmbientSylowSubgroup Kg Q2 =
        ⊥ := by
    simpa [K, Kg] using
      (lemma_11_1_a (M := M) (A0 := A0) (A := A) (p := p) (P := P)
        h11 (g := g) hgM hAgM hqσ Q1 Q2 hAQ1 hAQ2)
  have hR0_le_bot : R0G ≤ ⊥ := by
    have hR0_le_inf :
        R0G ≤ section10AmbientSylowSubgroup K Q1 ⊓
            section10AmbientSylowSubgroup Kg Q2 := by
      intro x hx
      exact ⟨hR0_le_Q1 hx, hR0_le_Q2 hx⟩
    simpa [hQinf_bot] using hR0_le_inf
  exact hR0G_ne_bot (le_bot_iff.mp hR0_le_bot)

end Section11
