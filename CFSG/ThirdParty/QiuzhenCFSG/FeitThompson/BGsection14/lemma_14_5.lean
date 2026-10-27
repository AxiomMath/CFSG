module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection14.theorem_14_4

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Lemma 14 5 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [IsMinCE G] in
public theorem CFSG.section14_sigmaLength_one_ne_one
    {x : G} (hx : section14SigmaLength x = 1) :
    x ≠ 1 := by
  intro h1
  have hbot : subgroupPrimeSet (Subgroup.zpowers x) = ∅ := by
    simpa [h1] using (show subgroupPrimeSet (⊥ : Subgroup G) = ∅ by
      ext p
      simp [subgroupPrimeSet, p.2.ne_one])
  simp [section14SigmaLength, section14SigmaSupport, section14ElementPrimeSupport, hbot] at hx

public theorem CFSG.section14_nonsingleton_of_mem_R_ne_one
    {x r : G} (hr : r ∈ section14R x) (hrne : r ≠ 1) :
    x ≠ 1 ∧ (section14MsigmaElement x).Nonempty ∧
      1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x} := by
  have hx : x ≠ 1 := by
    intro hx1
    have hr1 : r = 1 := by
      simpa [section14R, hx1] using hr
    exact hrne hr1
  by_cases hσ : (section14MsigmaElement x).Nonempty
  · by_cases hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x}
    · exact ⟨hx, hσ, hcard⟩
    · have hcard' :
          ¬ 1 < (section14MsigmaElement x).ncard := by
        simpa only [Nat.card_coe_set_eq] using hcard
      have hr1 : r = 1 := by
        simpa [section14R, hx, hσ, hcard'] using hr
      exact False.elim (hrne hr1)
  · have hr1 : r = 1 := by
      simpa [section14R, hx, hσ] using hr
    exact False.elim (hrne hr1)

omit [IsMinCE G] in
public theorem CFSG.section14_unique_sigma_block_of_length_one
    {x : G} (hx : section14SigmaLength x = 1) :
    ∃! π : Set Nat.Primes, π ∈ section14SigmaSupport x := by
  have hcard : Nat.card ↥(section14SigmaSupport x) = 1 := by
    simpa [section14SigmaLength] using hx
  have hsub : Subsingleton ↥(section14SigmaSupport x) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  have hnonempty : Nonempty ↥(section14SigmaSupport x) :=
    (Nat.card_eq_one_iff_unique.mp hcard).2
  rcases hnonempty with ⟨π, hπ⟩
  refine ⟨π, hπ, ?_⟩
  intro π' hπ'
  exact congrArg Subtype.val
    (show (⟨π', hπ'⟩ : section14SigmaSupport x) = ⟨π, hπ⟩ from
      Subsingleton.elim _ _)

public theorem CFSG.section14_primeSupport_subset_sigma_of_msigmaMember
    {x : G} {M : Subgroup G} (hM : M ∈ section14MsigmaElement x) :
    section14ElementPrimeSupport x ⊆ section10SigmaPrimes M := by
  intro p hp
  exact ((theorem_10_2_b (G := G) hM.1).1).p_in_pi_of_p_dvd_card p <|
    section8_subgroupPrimeSet_mono
      (Subgroup.zpowers_le.2 (hM.2 (by simp))) hp

public theorem CFSG.section14_mem_msigma_of_primeSupport_subset
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {x : G} (hxM : x ∈ M)
    (hxσ : section14ElementPrimeSupport x ⊆ section10SigmaPrimes M) :
    x ∈ section10Msigma M := by
  let q : M →* M ⧸ section10MsigmaSubgroup M :=
    QuotientGroup.mk' (section10MsigmaSubgroup M)
  have hxQ_dvd_order : orderOf (q ⟨x, hxM⟩) ∣ orderOf x := by
    simpa [q] using orderOf_map_dvd (ψ := q) ⟨x, hxM⟩
  have hxQ_dvd_index : orderOf (q ⟨x, hxM⟩) ∣ (section10MsigmaSubgroup M).index := by
    have hxQ_dvd_card :
        orderOf (q ⟨x, hxM⟩) ∣ Nat.card (M ⧸ section10MsigmaSubgroup M) := by
      simpa using orderOf_dvd_natCard (q ⟨x, hxM⟩)
    simpa [Subgroup.index_eq_card] using hxQ_dvd_card
  have hcop : Nat.Coprime (orderOf x) (section10MsigmaSubgroup M).index := by
    refine Nat.coprime_of_dvd ?_
    intro p hpprime hpx hpidx
    let p' : Nat.Primes := ⟨p, hpprime⟩
    have hpSupp : p' ∈ section14ElementPrimeSupport x := by
      simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hpx
    have hpσ : p' ∈ section10SigmaPrimes M := hxσ hpSupp
    exact (((theorem_10_2_b (G := G) hM).2).p_in_pi_of_p_dvd_index p' hpidx) hpσ
  have hxQ1 : orderOf (q ⟨x, hxM⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hxQ_dvd_order hxQ_dvd_index
  have hxQeq1 : q ⟨x, hxM⟩ = 1 := (orderOf_eq_one_iff).mp hxQ1
  rw [section10Msigma, Subgroup.mem_map]
  refine ⟨⟨x, hxM⟩, ?_, rfl⟩
  simpa [q, QuotientGroup.ker_mk'] using
    (MonoidHom.mem_ker (f := q) (x := ⟨x, hxM⟩)).2 hxQeq1

public theorem CFSG.section14_primeSupport_subset_sigmaN_of_mem_R
    {x r : G} (hr : r ∈ section14R x) :
    section14ElementPrimeSupport r ⊆ section10SigmaPrimes (section14N x) := by
  by_cases hr1 : r = 1
  · intro p hp
    have hbot : section14ElementPrimeSupport r = ∅ := by
      ext q
      simp [section14ElementPrimeSupport, hr1, subgroupPrimeSet, q.2.ne_one]
    simp [hbot] at hp
  · obtain ⟨hx, hσ, hcard⟩ := section14_nonsingleton_of_mem_R_ne_one hr hr1
    let M : Subgroup G := Classical.choose hσ
    have hM : M ∈ section14MsigmaElement x := Classical.choose_spec hσ
    have hRdef :=
      (theorem_14_4_a (G := G) (x := x) hx hσ hcard hM).1
    have hrCx : r ∈ elementCentralizerIn (section10Msigma (section14N x)) x := by
      simpa [hRdef] using hr
    intro p hp
    exact ((theorem_10_2_b (G := G)
      (section14N_mem_of_nonsingleton hx hσ hcard).1).1).p_in_pi_of_p_dvd_card p <|
        section8_subgroupPrimeSet_mono
          (Subgroup.zpowers_le.2 hrCx.1) hp

omit [IsMinCE G] in
public theorem CFSG.section14_sigma_mem_conjBy
    {L : Subgroup G} {p : Nat.Primes}
    (hpσ : p ∈ section10SigmaPrimes L) (a : G) :
    p ∈ section10SigmaPrimes (L.conjBy a) := by
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases hpσ with ⟨hpL, P, hN⟩
  let PG : Subgroup G := section10AmbientSylowSubgroup L P
  let PGa : Subgroup G := PG.conjBy a
  have hPG_le_L : PG ≤ L := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
    exact z.property
  have hPGa_le_La : PGa ≤ L.conjBy a := by
    intro y hy
    change y ∈ PG.conjBy a at hy
    rw [Subgroup.conjBy, Subgroup.mem_map] at hy
    rw [Subgroup.conjBy, Subgroup.mem_map]
    rcases hy with ⟨z, hz, rfl⟩
    exact ⟨z, hPG_le_L hz, rfl⟩
  have hPG_card : Nat.card PG = Nat.card (P : Subgroup L) := by
    simpa [PG, section10AmbientSylowSubgroup] using
      (Subgroup.card_map_of_injective
        (K := (P : Subgroup L)) (f := L.subtype) L.subtype_injective)
  let Psub : Subgroup (L.conjBy a) := PGa.subgroupOf (L.conjBy a)
  have hPsub_card :
      Nat.card Psub = p.val ^ (Nat.card (L.conjBy a)).factorization p.val := by
    calc
      Nat.card Psub = Nat.card PGa := by
        simpa [Psub] using natCard_subgroupOf_eq PGa (L.conjBy a) hPGa_le_La
      _ = Nat.card PG := by
        simpa [PGa] using section14_card_conjBy (G := G) PG a
      _ = Nat.card (P : Subgroup L) := by
        exact hPG_card
      _ = p.val ^ (Nat.card L).factorization p.val := Sylow.card_eq_multiplicity P
      _ = p.val ^ (Nat.card (L.conjBy a)).factorization p.val := by
        rw [section14_card_conjBy (G := G) L a]
  let P' : Sylow p.val (L.conjBy a) := Sylow.ofCard Psub hPsub_card
  have hP'_ambient : section10AmbientSylowSubgroup (L.conjBy a) P' = PGa := by
    calc
      section10AmbientSylowSubgroup (L.conjBy a) P' =
          (Psub.map (L.conjBy a).subtype : Subgroup G) := by
            simp [section10AmbientSylowSubgroup, P']
      _ = PGa ⊓ L.conjBy a := Subgroup.subgroupOf_map_subtype PGa (L.conjBy a)
      _ = PGa := inf_eq_left.mpr hPGa_le_La
  refine ⟨?_, P', ?_⟩
  · change p.val ∣ Nat.card (L.conjBy a)
    rw [section14_card_conjBy (G := G) L a]
    exact hpL
  · intro n hn
    have hnPGa : n ∈ Subgroup.normalizer (PGa : Set G) := by
      simpa [hP'_ambient] using hn
    have hPG_fix : PG.conjBy (a⁻¹ * n * a) = PG := by
      have hn_eq : PGa.conjBy n = PGa :=
        section11_conjBy_eq_of_mem_normalizer (H := PGa) hnPGa
      calc
        PG.conjBy (a⁻¹ * n * a) =
            (PG.conjBy (n * a)).conjBy a⁻¹ := by
              simpa [mul_assoc] using
                (section11_conjBy_conjBy (G := G) PG (n * a) a⁻¹).symm
        _ = ((PG.conjBy a).conjBy n).conjBy a⁻¹ := by
              rw [(section11_conjBy_conjBy (G := G) PG a n).symm]
        _ = (PG.conjBy a).conjBy a⁻¹ := by
              rw [show (PG.conjBy a).conjBy n = PG.conjBy a by
                simpa [PGa] using hn_eq]
        _ = PG := section11_conjBy_inv (G := G) PG a
    have hconj :
        a⁻¹ * n * a ∈ Subgroup.normalizer (PG : Set G) :=
      section14_mem_normalizer_of_conjBy_eq (G := G) (H := PG) hPG_fix
    have hnL : a⁻¹ * n * a ∈ L := hN hconj
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨a⁻¹ * n * a, hnL, by simp [mul_assoc]⟩

public theorem CFSG.section14_sigmaSupport_eq_singleton_of_length_one
    {x : G} (hx : section14SigmaLength x = 1)
    {M : Subgroup G} (hM : M ∈ section14MsigmaElement x) :
    section14SigmaSupport x = {section10SigmaPrimes M} := by
  have hxσM : section14ElementPrimeSupport x ⊆ section10SigmaPrimes M :=
    section14_primeSupport_subset_sigma_of_msigmaMember hM
  have hne : x ≠ 1 := section14_sigmaLength_one_ne_one hx
  obtain ⟨q, z, hz_zpowx, _hz_Mσ, hz_ne, hzprime⟩ :=
    section14_exists_primeOrder_zpowers_in (G := G)
      (B := section10Msigma M) (hM.2 (by simp)) hne
  have hqSupp : q ∈ section14ElementPrimeSupport x := by
    have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
      rw [subgroupPrimeSet]
      rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
        ⟨_hzle, hqcard⟩
      simp [hqcard]
    simpa [section14ElementPrimeSupport] using
      section8_subgroupPrimeSet_mono
        (Subgroup.zpowers_le.2 hz_zpowx) hqz
  have hnonemptyMeet :
      (section14ElementPrimeSupport x ∩ section10SigmaPrimes M).Nonempty :=
    ⟨q, hqSupp, hxσM hqSupp⟩
  have sigma_mem_conjBy :
      ∀ {L : Subgroup G} {p : Nat.Primes},
        p ∈ section10SigmaPrimes L → ∀ a : G,
          p ∈ section10SigmaPrimes (L.conjBy a) := by
    intro L p hpσ a
    haveI : Fact p.val.Prime := ⟨p.property⟩
    rcases hpσ with ⟨hpL, P, hN⟩
    let PG : Subgroup G := section10AmbientSylowSubgroup L P
    let PGa : Subgroup G := PG.conjBy a
    have hPG_le_L : PG ≤ L := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
      exact z.property
    have hPGa_le_La : PGa ≤ L.conjBy a := by
      intro y hy
      change y ∈ PG.conjBy a at hy
      rw [Subgroup.conjBy, Subgroup.mem_map] at hy
      rw [Subgroup.conjBy, Subgroup.mem_map]
      rcases hy with ⟨z, hz, rfl⟩
      exact ⟨z, hPG_le_L hz, rfl⟩
    have hPG_card : Nat.card PG = Nat.card (P : Subgroup L) := by
      simpa [PG, section10AmbientSylowSubgroup] using
        (Subgroup.card_map_of_injective
          (K := (P : Subgroup L)) (f := L.subtype) L.subtype_injective)
    let Psub : Subgroup (L.conjBy a) := PGa.subgroupOf (L.conjBy a)
    have hPsub_card :
        Nat.card Psub = p.val ^ (Nat.card (L.conjBy a)).factorization p.val := by
      calc
        Nat.card Psub = Nat.card PGa := by
          simpa [Psub] using natCard_subgroupOf_eq PGa (L.conjBy a) hPGa_le_La
        _ = Nat.card PG := by
          simpa [PGa] using section14_card_conjBy (G := G) PG a
        _ = Nat.card (P : Subgroup L) := by
          exact hPG_card
        _ = p.val ^ (Nat.card L).factorization p.val := Sylow.card_eq_multiplicity P
        _ = p.val ^ (Nat.card (L.conjBy a)).factorization p.val := by
          rw [section14_card_conjBy (G := G) L a]
    let P' : Sylow p.val (L.conjBy a) := Sylow.ofCard Psub hPsub_card
    have hP'_ambient : section10AmbientSylowSubgroup (L.conjBy a) P' = PGa := by
      calc
        section10AmbientSylowSubgroup (L.conjBy a) P' =
            (Psub.map (L.conjBy a).subtype : Subgroup G) := by
              simp [section10AmbientSylowSubgroup, P']
        _ = PGa ⊓ L.conjBy a := Subgroup.subgroupOf_map_subtype PGa (L.conjBy a)
        _ = PGa := inf_eq_left.mpr hPGa_le_La
    refine ⟨?_, P', ?_⟩
    · change p.val ∣ Nat.card (L.conjBy a)
      rw [section14_card_conjBy (G := G) L a]
      exact hpL
    · intro n hn
      have hnPGa : n ∈ Subgroup.normalizer (PGa : Set G) := by
        simpa [hP'_ambient] using hn
      have hPG_fix : PG.conjBy (a⁻¹ * n * a) = PG := by
        have hn_eq : PGa.conjBy n = PGa :=
          section11_conjBy_eq_of_mem_normalizer (H := PGa) hnPGa
        calc
          PG.conjBy (a⁻¹ * n * a) =
              (PG.conjBy (n * a)).conjBy a⁻¹ := by
                simpa [mul_assoc] using
                  (section11_conjBy_conjBy (G := G) PG (n * a) a⁻¹).symm
          _ = ((PG.conjBy a).conjBy n).conjBy a⁻¹ := by
                rw [(section11_conjBy_conjBy (G := G) PG a n).symm]
          _ = (PG.conjBy a).conjBy a⁻¹ := by
                rw [show (PG.conjBy a).conjBy n = PG.conjBy a by
                  simpa [PGa] using hn_eq]
          _ = PG := section11_conjBy_inv (G := G) PG a
      have hconj :
          a⁻¹ * n * a ∈ Subgroup.normalizer (PG : Set G) :=
        section14_mem_normalizer_of_conjBy_eq (G := G) (H := PG) hPG_fix
      have hnL : a⁻¹ * n * a ∈ L := hN hconj
      rw [Subgroup.conjBy, Subgroup.mem_map]
      exact ⟨a⁻¹ * n * a, hnL, by simp [mul_assoc]⟩
  ext π
  constructor
  · intro hπ
    rcases hπ with ⟨hπblock, hmeet⟩
    rcases hπblock with ⟨H, hH, rfl⟩
    rcases hmeet with ⟨p, hpSupp, hpHσ⟩
    have hpMσ : p ∈ section10SigmaPrimes M := hxσM hpSupp
    by_cases hconj : section14ConjugateSubgroups H M
    · rcases hconj with ⟨g, hHg⟩
      have hσeq : section10SigmaPrimes H = section10SigmaPrimes M := by
        ext s
        constructor
        · intro hs
          have hsHg : s ∈ section10SigmaPrimes (M.conjBy g) := by
            simpa [hHg] using hs
          have hsBack :
              s ∈ section10SigmaPrimes ((M.conjBy g).conjBy g⁻¹) :=
            sigma_mem_conjBy hsHg g⁻¹
          simpa [section11_conjBy_inv] using hsBack
        · intro hs
          have hsForw : s ∈ section10SigmaPrimes (M.conjBy g) :=
            sigma_mem_conjBy hs g
          simpa [hHg] using hsForw
      simp [hσeq]
    · have hHnot : section12NotConjugate H M := by
        intro g hHg
        exact hconj ⟨g⁻¹, by
          simpa [section11_conjBy_inv] using
            congrArg (fun K => K.conjBy g⁻¹) hHg⟩
      have hdisj : Disjoint (section10SigmaPrimes M) (section10SigmaPrimes H) :=
        theorem_13_9 (G := G) hM.1 hH hHnot
      exact False.elim ((Set.disjoint_left.mp hdisj) hpMσ hpHσ)
  · intro hπ
    rw [Set.mem_singleton_iff] at hπ
    subst hπ
    exact ⟨⟨M, hM.1, rfl⟩, hnonemptyMeet⟩

public theorem CFSG.section14_primeSupport_subset_tau2N_of_mem_R_ne_one
    {x r : G} (hr : r ∈ section14R x) (hrne : r ≠ 1) :
    section14ElementPrimeSupport x ⊆ section12Tau2Primes (section14N x) := by
  obtain ⟨hx, hσ, hcard⟩ := section14_nonsingleton_of_mem_R_ne_one hr hrne
  let M : Subgroup G := Classical.choose hσ
  have hM : M ∈ section14MsigmaElement x := Classical.choose_spec hσ
  exact (theorem_14_4_c (G := G) (x := x) hx hσ hcard hM).1

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_coprime_order_of_support_split
    {a b : G} {π : Set Nat.Primes}
    (ha : section14ElementPrimeSupport a ⊆ πᶜ)
    (hb : section14ElementPrimeSupport b ⊆ π) :
    Nat.Coprime (orderOf a) (orderOf b) := by
  refine Nat.coprime_of_dvd ?_
  intro l hlprime hla hlb
  let l' : Nat.Primes := ⟨l, hlprime⟩
  have hla' : l' ∈ section14ElementPrimeSupport a := by
    simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hla
  have hlb' : l' ∈ section14ElementPrimeSupport b := by
    simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hlb
  exact ha hla' (hb hlb')

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_mem_zpowers_mul_of_commute_of_coprime_order
    {a b : G} (hab : Commute a b)
    (hcop : Nat.Coprime (orderOf a) (orderOf b)) :
    a ∈ Subgroup.zpowers (a * b) := by
  have hbpow : b ^ orderOf b = 1 := pow_orderOf_eq_one b
  have hpow : (a * b) ^ orderOf b = a ^ orderOf b := by
    rw [hab.mul_pow, hbpow, mul_one]
  have hamem : a ∈ Subgroup.zpowers (a ^ orderOf b) := by
    rw [mem_zpowers_pow_iff]
    simpa [Nat.gcd_comm] using hcop.gcd_eq_one
  rcases hamem with ⟨n, hn⟩
  refine ⟨(orderOf b : ℤ) * n, ?_⟩
  calc
    (a * b) ^ ((orderOf b : ℤ) * n) =
        ((a * b) ^ (orderOf b : ℤ)) ^ n := by
          rw [zpow_mul]
    _ = ((a * b) ^ orderOf b) ^ n := by
          rw [zpow_natCast]
    _ = (a ^ orderOf b) ^ n := by
          rw [hpow]
    _ = a := by
          simpa using hn

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_eq_one_of_support_subset_and_compl
    {a : G} {π : Set Nat.Primes}
    (haπ : section14ElementPrimeSupport a ⊆ π)
    (haπc : section14ElementPrimeSupport a ⊆ πᶜ) :
    a = 1 := by
  have hcard_one : Nat.card (Subgroup.zpowers a) = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hpprime hpdiv
    let p' : Nat.Primes := ⟨p, hpprime⟩
    have hpπ : p' ∈ π := haπ hpdiv
    have hpπc : p' ∈ πᶜ := haπc hpdiv
    exact hpπc hpπ
  have horder_one : orderOf a = 1 := by
    simpa [Nat.card_zpowers] using hcard_one
  simpa [horder_one] using pow_orderOf_eq_one a

omit [IsMinCE G] in
public theorem CFSG.section14_mem_zpowers_right_of_support_subset
    {a b y : G} {π : Set Nat.Primes}
    (hab : Commute a b)
    (hcop : Nat.Coprime (orderOf a) (orderOf b))
    (haπc : section14ElementPrimeSupport a ⊆ πᶜ)
    (hbπ : section14ElementPrimeSupport b ⊆ π)
    (hy : y ∈ Subgroup.zpowers (a * b))
    (hyπ : section14ElementPrimeSupport y ⊆ π) :
    y ∈ Subgroup.zpowers b := by
  let C : Subgroup G := Subgroup.zpowers (a * b)
  have haC : Subgroup.zpowers a ≤ C := Subgroup.zpowers_le.2
    (section14_mem_zpowers_mul_of_commute_of_coprime_order hab hcop)
  have hbC : Subgroup.zpowers b ≤ C := by
    apply Subgroup.zpowers_le.2
    have hbmem : b ∈ Subgroup.zpowers (b * a) :=
      section14_mem_zpowers_mul_of_commute_of_coprime_order
        hab.symm (by simpa [Nat.coprime_comm] using hcop)
    simpa [C, hab.eq] using hbmem
  let A : Subgroup C := (Subgroup.zpowers a).subgroupOf C
  let B : Subgroup C := (Subgroup.zpowers b).subgroupOf C
  have hsup : C = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    apply le_antisymm
    · apply Subgroup.zpowers_le.2
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers b)
    · exact sup_le haC hbC
  have hABtop : A ⊔ B = ⊤ := by
    calc
      A ⊔ B = (Subgroup.zpowers a ⊔ Subgroup.zpowers b).subgroupOf C := by
        symm
        exact Subgroup.subgroupOf_sup (A := Subgroup.zpowers a) (A' := Subgroup.zpowers b)
          (B := C) haC hbC
      _ = C.subgroupOf C := by rw [hsup]
      _ = ⊤ := by simp
  have hcopAB : Nat.Coprime (Nat.card (Subgroup.zpowers a)) (Nat.card (Subgroup.zpowers b)) := by
    simpa [Nat.card_zpowers] using hcop
  have hdisjAB : Disjoint A B := by
    have hcardA : Nat.card A = Nat.card (Subgroup.zpowers a) := by
      simpa [A] using natCard_subgroupOf_eq (Subgroup.zpowers a) C haC
    have hcardB : Nat.card B = Nat.card (Subgroup.zpowers b) := by
      simpa [B] using natCard_subgroupOf_eq (Subgroup.zpowers b) C hbC
    have hcopAB' : Nat.Coprime (Nat.card A) (Nat.card B) := by
      rw [hcardA, hcardB]
      exact hcopAB
    exact Subgroup.disjoint_of_coprime_natCard hcopAB'
  haveI : A.Normal := inferInstance
  have hyTop : (⟨y, hy⟩ : C) ∈ A ⊔ B := by
    simp [hABtop]
  rcases (Subgroup.mem_sup_of_normal_left (s := A) (t := B) (x := (⟨y, hy⟩ : C))).1 hyTop with
    ⟨u, huA, v, hvB, huv⟩
  have huA' : (u : G) ∈ Subgroup.zpowers a := by
    simpa [A, Subgroup.mem_subgroupOf] using huA
  have hvB' : (v : G) ∈ Subgroup.zpowers b := by
    simpa [B, Subgroup.mem_subgroupOf] using hvB
  have huv_eq : (u : G) * (v : G) = y := congrArg Subtype.val huv
  have huvComm : Commute (u : G) (v : G) := by
    change (u : G) * (v : G) = (v : G) * (u : G)
    exact setLike_mul_comm (s := C) u.property v.property
  have huπc : section14ElementPrimeSupport (u : G) ⊆ πᶜ := by
    intro p hp
    exact haπc (section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 huA') (by
      simpa [section14ElementPrimeSupport] using hp))
  have hvπ : section14ElementPrimeSupport (v : G) ⊆ π := by
    intro p hp
    exact hbπ (section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hvB') (by
      simpa [section14ElementPrimeSupport] using hp))
  have huvCop : Nat.Coprime (orderOf (u : G)) (orderOf (v : G)) :=
    section14_coprime_order_of_support_split huπc hvπ
  have huY : (u : G) ∈ Subgroup.zpowers y := by
    have huMem :
        (u : G) ∈ Subgroup.zpowers ((u : G) * (v : G)) :=
      section14_mem_zpowers_mul_of_commute_of_coprime_order huvComm huvCop
    simpa [huv_eq] using huMem
  have huπ : section14ElementPrimeSupport (u : G) ⊆ π := by
    intro p hp
    exact hyπ (section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 huY) (by
      simpa [section14ElementPrimeSupport] using hp))
  have hu_one : (u : G) = 1 :=
    section14_eq_one_of_support_subset_and_compl huπ huπc
  have hy_eq_v : y = (v : G) := by
    have hv_eq_y : (v : G) = y := by
      simpa [hu_one] using huv_eq
    exact hv_eq_y.symm
  exact hy_eq_v ▸ hvB'

omit [IsMinCE G] in
public theorem CFSG.section14_mem_zpowers_left_of_support_subset
    {a b y : G} {π : Set Nat.Primes}
    (hab : Commute a b)
    (hcop : Nat.Coprime (orderOf a) (orderOf b))
    (haπc : section14ElementPrimeSupport a ⊆ πᶜ)
    (hbπ : section14ElementPrimeSupport b ⊆ π)
    (hy : y ∈ Subgroup.zpowers (a * b))
    (hyπc : section14ElementPrimeSupport y ⊆ πᶜ) :
    y ∈ Subgroup.zpowers a := by
  have hyInv : y ∈ Subgroup.zpowers (b * a) := by
    simpa [hab.eq] using hy
  exact section14_mem_zpowers_right_of_support_subset
    (a := b) (b := a) (y := y) (π := πᶜ) hab.symm
    (by simpa [Nat.coprime_comm] using hcop)
    (by
      intro p hp
      exact fun hpπc => hpπc (hbπ hp))
    haπc hyInv hyπc

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_isPiSubgroup_zpowers_of_support_subset
    {a : G} {π : Set Nat.Primes}
    (ha : section14ElementPrimeSupport a ⊆ π) :
    IsPiSubgroup (G := G) π (Subgroup.zpowers a) := by
  simpa [section14ElementPrimeSupport] using
    (section8_isPiSubgroup_of_subgroupPrimeSet_subset ha)

public theorem CFSG.section14_sigma_eq_of_common_prime
    {M H : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hH : H ∈ section9MaximalSubgroups G)
    {p : Nat.Primes}
    (hpM : p ∈ section10SigmaPrimes M)
    (hpH : p ∈ section10SigmaPrimes H) :
    section10SigmaPrimes M = section10SigmaPrimes H := by
  by_cases hconj : section14ConjugateSubgroups H M
  · rcases hconj with ⟨g, hHg⟩
    ext s
    constructor
    · intro hs
      have hsForw : s ∈ section10SigmaPrimes (M.conjBy g) :=
        section14_sigma_mem_conjBy hs g
      simpa [hHg] using hsForw
    · intro hs
      have hsHg : s ∈ section10SigmaPrimes (M.conjBy g) := by
        simpa [hHg] using hs
      have hsBack :
          s ∈ section10SigmaPrimes ((M.conjBy g).conjBy g⁻¹) :=
        section14_sigma_mem_conjBy hsHg g⁻¹
      simpa [section11_conjBy_inv] using hsBack
  · have hnot : section12NotConjugate H M := by
      intro g hHg
      exact hconj ⟨g⁻¹, by
        simpa [section11_conjBy_inv] using congrArg (fun K => K.conjBy g⁻¹) hHg⟩
    have hdisj : Disjoint (section10SigmaPrimes M) (section10SigmaPrimes H) :=
      theorem_13_9 (G := G) hM hH hnot
    exact False.elim ((Set.disjoint_left.mp hdisj) hpM hpH)

private theorem CFSG.section14_eq_or_mem_R_of_common_product
    {x y rx ry : G}
    (hx : section14SigmaLength x = 1)
    (hy : section14SigmaLength y = 1)
    (hrx : rx ∈ section14R x)
    (hry : ry ∈ section14R y)
    (hEq : x * rx = y * ry) :
    y = x ∨ y ∈ section14R x := by
  have hxne : x ≠ 1 := section14_sigmaLength_one_ne_one hx
  have hyne : y ≠ 1 := section14_sigmaLength_one_ne_one hy
  have support_dvd {a : G} {p : Nat.Primes}
      (hp : p ∈ section14ElementPrimeSupport a) :
      p.val ∣ orderOf a := by
    simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hp
  have dvd_support {a : G} {p : Nat.Primes}
      (hp : p.val ∣ orderOf a) :
      p ∈ section14ElementPrimeSupport a := by
    simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hp
  have support_mono {a b : G} (hab : a ∈ Subgroup.zpowers b) :
      section14ElementPrimeSupport a ⊆ section14ElementPrimeSupport b := by
    intro p hp
    exact section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hab) hp
  have sigma_unique {a : G} (ha : section14SigmaLength a = 1) :
      ∀ {π₁ π₂ : Set Nat.Primes},
        π₁ ∈ section14SigmaSupport a →
        π₂ ∈ section14SigmaSupport a → π₁ = π₂ := by
    obtain ⟨π0, hπ0, huniq⟩ := section14_unique_sigma_block_of_length_one ha
    intro π₁ π₂ h₁ h₂
    exact (huniq _ h₁).trans (huniq _ h₂).symm
  have support_subset_left_or_right
      {a : G} (ha : section14SigmaLength a = 1)
      {π₁ π₂ : Set Nat.Primes}
      (hπ₁ : π₁ ∈ section14SigmaBlocks G)
      (hπ₂ : π₂ ∈ section14SigmaBlocks G)
      (hdisj : Disjoint π₁ π₂)
      (hcover : section14ElementPrimeSupport a ⊆ π₁ ∪ π₂) :
      section14ElementPrimeSupport a ⊆ π₁ ∨
        section14ElementPrimeSupport a ⊆ π₂ := by
    obtain ⟨q, z, hz_zpowa, _hzA, _hz_ne, hzprime⟩ :=
      section14_exists_primeOrder_zpowers_in (G := G)
        (B := Subgroup.zpowers a) (Subgroup.mem_zpowers a)
        (section14_sigmaLength_one_ne_one ha)
    have hqA : q ∈ section14ElementPrimeSupport a := by
      have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
        rw [subgroupPrimeSet]
        rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
          ⟨_hzle, hqcard⟩
        simp [hqcard]
      simpa [section14ElementPrimeSupport] using
        section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hz_zpowa) hqz
    rcases hcover hqA with hq₁ | hq₂
    · left
      intro p hpA
      rcases hcover hpA with hp₁ | hp₂
      · exact hp₁
      · have hπ₁A : π₁ ∈ section14SigmaSupport a := ⟨hπ₁, ⟨q, hqA, hq₁⟩⟩
        have hπ₂A : π₂ ∈ section14SigmaSupport a := ⟨hπ₂, ⟨p, hpA, hp₂⟩⟩
        have hEqπ : π₁ = π₂ := sigma_unique ha hπ₁A hπ₂A
        exact False.elim ((Set.disjoint_left.mp hdisj) hq₁ (hEqπ ▸ hq₁))
    · right
      intro p hpA
      rcases hcover hpA with hp₁ | hp₂
      · have hπ₁A : π₁ ∈ section14SigmaSupport a := ⟨hπ₁, ⟨p, hpA, hp₁⟩⟩
        have hπ₂A : π₂ ∈ section14SigmaSupport a := ⟨hπ₂, ⟨q, hqA, hq₂⟩⟩
        have hEqπ : π₁ = π₂ := sigma_unique ha hπ₁A hπ₂A
        exact False.elim ((Set.disjoint_left.mp hdisj) hp₁ (hEqπ ▸ hp₁))
      · exact hp₂
  by_cases hrx1 : rx = 1
  · have hEqx : x = y * ry := by
      simpa [hrx1] using hEq
    by_cases hry1 : ry = 1
    · left
      simpa [hry1] using hEqx.symm
    · exfalso
      obtain ⟨_hy, hσy, hcardy⟩ := section14_nonsingleton_of_mem_R_ne_one hry hry1
      let My : Subgroup G := Classical.choose hσy
      have hMy : My ∈ section14MsigmaElement y := Classical.choose_spec hσy
      have hNy := section14N_mem_of_nonsingleton (x := y) hyne hσy hcardy
      let B : Set Nat.Primes := section10SigmaPrimes My
      let π : Set Nat.Primes := section10SigmaPrimes (section14N y)
      have hB_block : B ∈ section14SigmaBlocks G := ⟨My, hMy.1, rfl⟩
      have hπ_block : π ∈ section14SigmaBlocks G := ⟨section14N y, hNy.1, rfl⟩
      have hyB : section14ElementPrimeSupport y ⊆ B :=
        section14_primeSupport_subset_sigma_of_msigmaMember hMy
      have hryπ : section14ElementPrimeSupport ry ⊆ π := by
        simpa [π] using section14_primeSupport_subset_sigmaN_of_mem_R hry
      have hyπc : section14ElementPrimeSupport y ⊆ πᶜ := by
        intro p hpY hpπ
        rcases (by
          simpa [π, section12Tau2Primes] using
            section14_primeSupport_subset_tau2N_of_mem_R_ne_one hry hry1 hpY) with
          ⟨hp_not_π, _hprank⟩
        exact hp_not_π hpπ
      have hB_disj : Disjoint B π := by
        rw [Set.disjoint_left]
        intro p hpB hpπ
        have hEqπ : B = π :=
          section14_sigma_eq_of_common_prime hMy.1 hNy.1 hpB hpπ
        have hyπ : section14ElementPrimeSupport y ⊆ π := by
          simpa [B, hEqπ] using hyB
        exact hyne (section14_eq_one_of_support_subset_and_compl hyπ hyπc)
      have hRdefy :=
        (theorem_14_4_a (G := G) (x := y) hyne hσy hcardy hMy).1
      have hryCy : ry ∈ elementCentralizerIn (section10Msigma (section14N y)) y := by
        simpa [hRdefy] using hry
      have hyrComm : Commute y ry := by
        exact (Subgroup.mem_centralizer_singleton_iff.mp hryCy.2).symm
      have hcopy : Nat.Coprime (orderOf y) (orderOf ry) :=
        section14_coprime_order_of_support_split hyπc hryπ
      have hcoverX : section14ElementPrimeSupport x ⊆ B ∪ π := by
        intro p hpX
        have hpX' : p.val ∣ orderOf (y * ry) := by
          simpa [hEqx] using support_dvd hpX
        have hpMul : p.val ∣ orderOf y * orderOf ry := by
          simpa [hyrComm.orderOf_mul_eq_mul_orderOf_of_coprime hcopy] using hpX'
        rcases p.property.dvd_or_dvd hpMul with hpY | hpRy
        · exact Or.inl (hyB (dvd_support hpY))
        · exact Or.inr (hryπ (dvd_support hpRy))
      rcases support_subset_left_or_right hx hB_block hπ_block hB_disj hcoverX with hxB | hxπ
      · have hxπc : section14ElementPrimeSupport x ⊆ πᶜ := by
          intro p hpX hpπ
          exact (Set.disjoint_left.mp hB_disj) (hxB hpX) hpπ
        have hxZpowY : x ∈ Subgroup.zpowers y :=
          section14_mem_zpowers_left_of_support_subset
            (a := y) (b := ry) (y := x)
            hyrComm hcopy hyπc hryπ
            (by simp [hEqx])
            hxπc
        have hryZpowY : ry ∈ Subgroup.zpowers y := by
          have hxy : y * ry ∈ Subgroup.zpowers y := hEqx ▸ hxZpowY
          simpa using
            (Subgroup.zpowers y).mul_mem
              ((Subgroup.zpowers y).inv_mem (Subgroup.mem_zpowers y)) hxy
        have hryB : section14ElementPrimeSupport ry ⊆ B := by
          intro p hpRy
          exact hyB (support_mono hryZpowY hpRy)
        have hryBc : section14ElementPrimeSupport ry ⊆ Bᶜ := by
          intro p hpRy hpB
          exact (Set.disjoint_left.mp hB_disj) hpB (hryπ hpRy)
        exact hry1 (section14_eq_one_of_support_subset_and_compl hryB hryBc)
      · have hxZpowRy : x ∈ Subgroup.zpowers ry :=
          section14_mem_zpowers_right_of_support_subset
            (a := y) (b := ry) (y := x)
            hyrComm hcopy hyπc hryπ
            (by simp [hEqx])
            hxπ
        have hyZpowRy : y ∈ Subgroup.zpowers ry := by
          have hxy : y * ry ∈ Subgroup.zpowers ry := hEqx ▸ hxZpowRy
          simpa using
            (Subgroup.zpowers ry).mul_mem hxy
              ((Subgroup.zpowers ry).inv_mem (Subgroup.mem_zpowers ry))
        have hyπ : section14ElementPrimeSupport y ⊆ π := by
          intro p hpY
          exact hryπ (support_mono hyZpowRy hpY)
        exact hyne (section14_eq_one_of_support_subset_and_compl hyπ hyπc)
  · have hrxne : rx ≠ 1 := hrx1
    obtain ⟨_hx, hσx, hcardx⟩ := section14_nonsingleton_of_mem_R_ne_one hrx hrxne
    let Mx : Subgroup G := Classical.choose hσx
    have hMx : Mx ∈ section14MsigmaElement x := Classical.choose_spec hσx
    have hNx := section14N_mem_of_nonsingleton (x := x) hxne hσx hcardx
    let Bx : Set Nat.Primes := section10SigmaPrimes Mx
    let π : Set Nat.Primes := section10SigmaPrimes (section14N x)
    have hBx_block : Bx ∈ section14SigmaBlocks G := ⟨Mx, hMx.1, rfl⟩
    have hπ_block : π ∈ section14SigmaBlocks G := ⟨section14N x, hNx.1, rfl⟩
    have hxBx : section14ElementPrimeSupport x ⊆ Bx :=
      section14_primeSupport_subset_sigma_of_msigmaMember hMx
    have hrxπ : section14ElementPrimeSupport rx ⊆ π := by
      simpa [π] using section14_primeSupport_subset_sigmaN_of_mem_R hrx
    have hxπc : section14ElementPrimeSupport x ⊆ πᶜ := by
      intro p hpX hpπ
      rcases (by
        simpa [π, section12Tau2Primes] using
          section14_primeSupport_subset_tau2N_of_mem_R_ne_one hrx hrxne hpX) with
        ⟨hp_not_π, _hprank⟩
      exact hp_not_π hpπ
    have hBx_disj : Disjoint Bx π := by
      rw [Set.disjoint_left]
      intro p hpBx hpπ
      have hEqπ : Bx = π :=
        section14_sigma_eq_of_common_prime hMx.1 hNx.1 hpBx hpπ
      have hxπ : section14ElementPrimeSupport x ⊆ π := by
        simpa [Bx, hEqπ] using hxBx
      exact hxne (section14_eq_one_of_support_subset_and_compl hxπ hxπc)
    have hRdefx :=
      (theorem_14_4_a (G := G) (x := x) hxne hσx hcardx hMx).1
    have hrxCx : rx ∈ elementCentralizerIn (section10Msigma (section14N x)) x := by
      simpa [hRdefx] using hrx
    have hxrComm : Commute x rx := by
      exact (Subgroup.mem_centralizer_singleton_iff.mp hrxCx.2).symm
    have hcopx : Nat.Coprime (orderOf x) (orderOf rx) :=
      section14_coprime_order_of_support_split hxπc hrxπ
    have hcover_of_memG {a : G} (haG : a ∈ Subgroup.zpowers (x * rx)) :
        section14ElementPrimeSupport a ⊆ Bx ∪ π := by
      intro p hpA
      have hpG : p.val ∣ orderOf (x * rx) := by
        exact support_dvd (support_mono haG hpA)
      have hpMul : p.val ∣ orderOf x * orderOf rx := by
        simpa [hxrComm.orderOf_mul_eq_mul_orderOf_of_coprime hcopx] using hpG
      rcases p.property.dvd_or_dvd hpMul with hpX | hpRx
      · exact Or.inl (hxBx (dvd_support hpX))
      · exact Or.inr (hrxπ (dvd_support hpRx))
    by_cases hry1 : ry = 1
    · have hyG : y ∈ Subgroup.zpowers (x * rx) := by
        have hyEq : y = x * rx := by
          simpa [hry1] using hEq.symm
        exact hyEq ▸ Subgroup.mem_zpowers (x * rx)
      rcases support_subset_left_or_right hy hBx_block hπ_block hBx_disj
          (hcover_of_memG hyG) with hyBx | hyπ
      · have hyπc : section14ElementPrimeSupport y ⊆ πᶜ := by
          intro p hpY hpπ
          exact (Set.disjoint_left.mp hBx_disj) (hyBx hpY) hpπ
        have hyZpowX : y ∈ Subgroup.zpowers x :=
          section14_mem_zpowers_left_of_support_subset
            (a := x) (b := rx) (y := y)
            hxrComm hcopx hxπc hrxπ hyG hyπc
        have hyEq : y = x * rx := by
          simpa [hry1] using hEq.symm
        have hrxZpowX : rx ∈ Subgroup.zpowers x := by
          have hxy : x * rx ∈ Subgroup.zpowers x := hyEq ▸ hyZpowX
          simpa using
            (Subgroup.zpowers x).mul_mem
              ((Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x)) hxy
        have hrxBx : section14ElementPrimeSupport rx ⊆ Bx := by
          intro p hpRx
          exact hxBx (support_mono hrxZpowX hpRx)
        have hrxBxc : section14ElementPrimeSupport rx ⊆ Bxᶜ := by
          intro p hpRx hpBx
          exact (Set.disjoint_left.mp hBx_disj) hpBx (hrxπ hpRx)
        exact False.elim
          (hrxne (section14_eq_one_of_support_subset_and_compl hrxBx hrxBxc))
      · exact Or.inr <| (Subgroup.zpowers_le.2 hrx)
          (section14_mem_zpowers_right_of_support_subset
            (a := x) (b := rx) (y := y)
            hxrComm hcopx hxπc hrxπ hyG hyπ)
    · obtain ⟨_hy, hσy, hcardy⟩ := section14_nonsingleton_of_mem_R_ne_one hry hry1
      let My : Subgroup G := Classical.choose hσy
      have hMy : My ∈ section14MsigmaElement y := Classical.choose_spec hσy
      have hNy := section14N_mem_of_nonsingleton (x := y) hyne hσy hcardy
      let πy : Set Nat.Primes := section10SigmaPrimes (section14N y)
      have hyπy_c : section14ElementPrimeSupport y ⊆ πyᶜ := by
        intro p hpY hpπy
        rcases (by
          simpa [πy, section12Tau2Primes] using
            section14_primeSupport_subset_tau2N_of_mem_R_ne_one hry hry1 hpY) with
          ⟨hp_not_πy, _hprank⟩
        exact hp_not_πy hpπy
      have hryπy : section14ElementPrimeSupport ry ⊆ πy := by
        simpa [πy] using section14_primeSupport_subset_sigmaN_of_mem_R hry
      have hRdefy :=
        (theorem_14_4_a (G := G) (x := y) hyne hσy hcardy hMy).1
      have hryCy : ry ∈ elementCentralizerIn (section10Msigma (section14N y)) y := by
        simpa [hRdefy] using hry
      have hyrComm : Commute y ry := by
        exact (Subgroup.mem_centralizer_singleton_iff.mp hryCy.2).symm
      have hcopy : Nat.Coprime (orderOf y) (orderOf ry) :=
        section14_coprime_order_of_support_split hyπy_c hryπy
      have hyG : y ∈ Subgroup.zpowers (x * rx) := by
        have hyG0 : y ∈ Subgroup.zpowers (y * ry) :=
          section14_mem_zpowers_mul_of_commute_of_coprime_order hyrComm hcopy
        simpa [hEq] using hyG0
      have hryG : ry ∈ Subgroup.zpowers (x * rx) := by
        have hryG0 : ry ∈ Subgroup.zpowers (ry * y) :=
          section14_mem_zpowers_mul_of_commute_of_coprime_order
            hyrComm.symm (by simpa [Nat.coprime_comm] using hcopy)
        have hryG1 : ry ∈ Subgroup.zpowers (y * ry) := by
          simpa [hyrComm.eq] using hryG0
        simpa [hEq] using hryG1
      rcases support_subset_left_or_right hy hBx_block hπ_block hBx_disj
          (hcover_of_memG hyG) with hyBx | hyπ
      · have hyπc : section14ElementPrimeSupport y ⊆ πᶜ := by
          intro p hpY hpπ
          exact (Set.disjoint_left.mp hBx_disj) (hyBx hpY) hpπ
        have hyZpowX : y ∈ Subgroup.zpowers x :=
          section14_mem_zpowers_left_of_support_subset
            (a := x) (b := rx) (y := y)
            hxrComm hcopx hxπc hrxπ hyG hyπc
        have hryπ : section14ElementPrimeSupport ry ⊆ π := by
          intro p hpRy
          rcases hcover_of_memG hryG hpRy with hpBx | hpπ
          · have hpπy : p ∈ πy := hryπy hpRy
            have hEqπy : Bx = πy :=
              section14_sigma_eq_of_common_prime hMx.1 hNy.1 hpBx hpπy
            have hyπy : section14ElementPrimeSupport y ⊆ πy := by
              simpa [Bx, hEqπy] using hyBx
            exact False.elim (hyne (section14_eq_one_of_support_subset_and_compl hyπy hyπy_c))
          · exact hpπ
        have hryZpowRx : ry ∈ Subgroup.zpowers rx :=
          section14_mem_zpowers_right_of_support_subset
            (a := x) (b := rx) (y := ry)
            hxrComm hcopx hxπc hrxπ hryG hryπ
        have hdisjxr : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers rx) := by
          have hcopCard :
              Nat.Coprime (Nat.card (Subgroup.zpowers x))
                (Nat.card (Subgroup.zpowers rx)) := by
            simpa [Nat.card_zpowers] using hcopx
          exact Subgroup.disjoint_of_coprime_natCard hcopCard
        exact Or.inl
          (section14_b1_left_eq_of_mul_eq_of_disjoint
            (G := G) hdisjxr
            hyZpowX hryZpowRx (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers rx)
            hEq.symm)
      · exact Or.inr <| (Subgroup.zpowers_le.2 hrx)
          (section14_mem_zpowers_right_of_support_subset
            (a := x) (b := rx) (y := y)
            hxrComm hcopx hxπc hrxπ hyG hyπ)

/-- Lemma 14.5(a): distinct `σ`-length one elements have disjoint `xR(x)`. -/
public theorem CFSG.lemma_14_5_a
    {x y : G} (hx : section14SigmaLength x = 1)
    (hy : section14SigmaLength y = 1) (hxy : x ≠ y) :
    section14ElementCoset x (section14R x) ∩
      section14ElementCoset y (section14R y) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro g hg
  rcases hg with ⟨hgx, hgy⟩
  rcases hgx with ⟨rx, hrx, rfl⟩
  rcases hgy with ⟨ry, hry, hEq⟩
  have hxne : x ≠ 1 := section14_sigmaLength_one_ne_one hx
  have hyne : y ≠ 1 := section14_sigmaLength_one_ne_one hy
  by_cases hyx : y = x
  · exact hxy hyx.symm
  · have hyRx : y ∈ section14R x := by
      rcases section14_eq_or_mem_R_of_common_product hx hy hrx hry hEq with rfl | hyRx
      · exact False.elim (hyx rfl)
      · exact hyRx
    have hxRy : x ∈ section14R y := by
      rcases section14_eq_or_mem_R_of_common_product hy hx hry hrx hEq.symm with hxy' | hxRy
      · exact False.elim (hyx hxy'.symm)
      · exact hxRy
    obtain ⟨_hx', hσx, hcardx⟩ := section14_nonsingleton_of_mem_R_ne_one hyRx hyne
    obtain ⟨_hy', hσy, hcardy⟩ := section14_nonsingleton_of_mem_R_ne_one hxRy hxne
    have hNx := section14N_mem_of_nonsingleton (x := x) hxne hσx hcardx
    have hNy := section14N_mem_of_nonsingleton (x := y) hyne hσy hcardy
    let Mx : Subgroup G := Classical.choose hσx
    let My : Subgroup G := Classical.choose hσy
    have hMx : Mx ∈ section14MsigmaElement x := Classical.choose_spec hσx
    have hMy : My ∈ section14MsigmaElement y := Classical.choose_spec hσy
    have hRdefx :=
      (theorem_14_4_a (G := G) (x := x) hxne hσx hcardx hMx).1
    have hRdefy :=
      (theorem_14_4_a (G := G) (x := y) hyne hσy hcardy hMy).1
    have hyNσx : y ∈ section10Msigma (section14N x) := by
      exact (show y ∈ elementCentralizerIn (section10Msigma (section14N x)) x by
        simpa [hRdefx] using hyRx).1
    have hxNσy : x ∈ section10Msigma (section14N y) := by
      exact (show x ∈ elementCentralizerIn (section10Msigma (section14N y)) y by
        simpa [hRdefy] using hxRy).1
    have hNyx : section14N y ∈ section14MsigmaElement x := by
      refine ⟨hNy.1, ?_⟩
      simpa using hxNσy
    have hcompx :=
      theorem_14_4_e (G := G) (x := x) hxne hσx hcardx hNyx
    have hyCx : y ∈ Subgroup.centralizer ({x} : Set G) := by
      exact (show y ∈ elementCentralizerIn (section10Msigma (section14N x)) x by
        simpa [hRdefx] using hyRx).2
    have hyNx : y ∈ section14N x := by
      exact hNx.2 hyCx
    have hyNy : y ∈ section14N y := by
      exact hNy.2 (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl y))
    have hyBot : y ∈ (⊥ : Subgroup G) := by
      exact Subgroup.disjoint_def.mp hcompx.2.2.2 hyNσx ⟨hyNy, hyNx⟩
    exact hyne (Subgroup.mem_bot.mp hyBot)

public theorem CFSG.section14_sigmaLength_one_of_mem_msigma
    {x : G} {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hxMσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1) :
    section14SigmaLength x = 1 := by
  have hMx : M ∈ section14MsigmaElement x := ⟨hM, by simpa using hxMσ⟩
  have hSigmaSupport :
      section14SigmaSupport x = {section10SigmaPrimes M} := by
    ext π
    constructor
    · intro hπ
      rcases hπ with ⟨hπblock, hmeet⟩
      rcases hπblock with ⟨H, hH, rfl⟩
      rcases hmeet with ⟨p, hpSupp, hpHσ⟩
      have hpMσ : p ∈ section10SigmaPrimes M :=
        section14_primeSupport_subset_sigma_of_msigmaMember hMx hpSupp
      have hσeq : section10SigmaPrimes H = section10SigmaPrimes M :=
        section14_sigma_eq_of_common_prime hH hM hpHσ hpMσ
      simp [hσeq]
    · intro hπ
      rw [Set.mem_singleton_iff] at hπ
      subst hπ
      obtain ⟨q, z, hz_zpowx, _hzMσ, _hz_ne, hzprime⟩ :=
        section14_exists_primeOrder_zpowers_in (G := G)
          (B := section10Msigma M) hxMσ hxne
      have hqSupp : q ∈ section14ElementPrimeSupport x := by
        have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
          rw [subgroupPrimeSet]
          rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
            ⟨_hzle, hqcard⟩
          simp [hqcard]
        simpa [section14ElementPrimeSupport] using
          section8_subgroupPrimeSet_mono
            (Subgroup.zpowers_le.2 hz_zpowx) hqz
      exact ⟨⟨M, hM, rfl⟩, ⟨q, hqSupp,
        section14_primeSupport_subset_sigma_of_msigmaMember hMx hqSupp⟩⟩
  simp [section14SigmaLength, hSigmaSupport]

/-- Lemma 14.5(b): nonconjugate maximal subgroups have disjoint `M̃`. -/
public theorem CFSG.lemma_14_5_b
    {M₁ M₂ : Subgroup G}
    (hM₁ : M₁ ∈ section9MaximalSubgroups G)
    (hM₂ : M₂ ∈ section9MaximalSubgroups G)
    (hnotconj : ¬ section14ConjugateSubgroups M₂ M₁) :
    section14Tilde M₂ ∩ section14Tilde M₁ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro g hg
  rcases hg with ⟨hg₂, hg₁⟩
  rcases hg₂ with ⟨x₂, hx₂Mσ, hx₂ne, r₂, hr₂, rfl⟩
  rcases hg₁ with ⟨x₁, hx₁Mσ, hx₁ne, r₁, hr₁, hEq⟩
  have hnot : section12NotConjugate M₂ M₁ := by
    intro a hMa
    exact hnotconj ⟨a⁻¹, by
      simpa [section11_conjBy_inv] using congrArg (fun K => K.conjBy a⁻¹) hMa⟩
  have hσdis : Disjoint (section10SigmaPrimes M₁) (section10SigmaPrimes M₂) :=
    theorem_13_9 (G := G) hM₁ hM₂ hnot
  have hx₁len : section14SigmaLength x₁ = 1 :=
    section14_sigmaLength_one_of_mem_msigma hM₁ hx₁Mσ hx₁ne
  have hx₂len : section14SigmaLength x₂ = 1 :=
    section14_sigmaLength_one_of_mem_msigma hM₂ hx₂Mσ hx₂ne
  by_cases hxx : x₂ = x₁
  · have hM₂x₁ : M₂ ∈ section14MsigmaElement x₁ := by
      refine ⟨hM₂, ?_⟩
      simpa [hxx] using hx₂Mσ
    have hM₁x₁ : M₁ ∈ section14MsigmaElement x₁ := ⟨hM₁, by simpa using hx₁Mσ⟩
    have hx₁σ₂ : section14ElementPrimeSupport x₁ ⊆ section10SigmaPrimes M₂ :=
      section14_primeSupport_subset_sigma_of_msigmaMember hM₂x₁
    have hx₁σ₁ : section14ElementPrimeSupport x₁ ⊆ section10SigmaPrimes M₁ :=
      section14_primeSupport_subset_sigma_of_msigmaMember hM₁x₁
    have hx₁σ₂c : section14ElementPrimeSupport x₁ ⊆ (section10SigmaPrimes M₂)ᶜ := by
      intro p hpX hpM₂
      exact (Set.disjoint_left.mp hσdis) (hx₁σ₁ hpX) hpM₂
    exact hx₁ne (section14_eq_one_of_support_subset_and_compl hx₁σ₂ hx₁σ₂c)
  · have hgCoset :
        x₂ * r₂ ∈ section14ElementCoset x₂ (section14R x₂) ∩
          section14ElementCoset x₁ (section14R x₁) := by
      refine ⟨?_, ?_⟩
      · exact ⟨r₂, hr₂, rfl⟩
      · exact ⟨r₁, hr₁, hEq⟩
    exact
      (Set.eq_empty_iff_forall_notMem.mp
        (lemma_14_5_a (x := x₂) (y := x₁) hx₂len hx₁len hxx))
        (x₂ * r₂) hgCoset


omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_maximal_conjBy
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) (g : G) :
    M.conjBy g ∈ section9MaximalSubgroups G := by
  have h_map : M.conjBy g = Subgroup.map ((MulAut.conj g : G ≃* G) : G →* G) M := rfl
  rw [h_map]
  exact ((MulAut.conj g : G ≃* G).mapSubgroup.isCoatom_iff M).mpr hM

omit [IsMinCE G] in
public theorem CFSG.section14_sigmaPrimes_conjBy
    (M : Subgroup G) (a : G) :
    section10SigmaPrimes (M.conjBy a) = section10SigmaPrimes M := by
  ext p
  constructor
  · intro hp
    have hpBack := section14_sigma_mem_conjBy (L := M.conjBy a) hp a⁻¹
    simpa [section11_conjBy_inv] using hpBack
  · intro hp
    exact section14_sigma_mem_conjBy (L := M) hp a

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_msigma_conjBy_subgroupOf
    (M : Subgroup G) (a : G) :
    let e : M ≃* M.conjBy a := (MulAut.conj a).subgroupMap M
    (((section10Msigma M).conjBy a).subgroupOf (M.conjBy a)) =
      (section10MsigmaSubgroup M).map e.toMonoidHom := by
  intro e
  ext x
  constructor
  · intro hx
    change (x : G) ∈ (section10Msigma M).conjBy a at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    rw [section10Msigma, Subgroup.mem_map] at hy
    rcases hy with ⟨z, hz, hzy⟩
    refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
    apply Subtype.ext
    have hzyG : (z : G) = y := hzy
    calc
      ((e z : M.conjBy a) : G) = a * (z : G) * a⁻¹ := by
        rfl
      _ = a * y * a⁻¹ := by rw [hzyG]
      _ = (x : G) := hyx
  · intro hx
    change (x : G) ∈ (section10Msigma M).conjBy a
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨z, hz, hzx⟩
    apply Subgroup.mem_map.mpr
    refine ⟨(z : G), ?_, ?_⟩
    · rw [section10Msigma, Subgroup.mem_map]
      exact ⟨z, hz, rfl⟩
    · change a * (z : G) * a⁻¹ = (x : G)
      have hzx' := congrArg Subtype.val hzx
      change ((e z : M.conjBy a) : G) = (x : G) at hzx'
      exact hzx'

omit [IsMinCE G] in
public theorem CFSG.section14_mem_msigma_conjBy
    {M : Subgroup G} {x a : G} (hx : x ∈ section10Msigma M) :
    a * x * a⁻¹ ∈ section10Msigma (M.conjBy a) := by
  let Kg : Subgroup G := (section10Msigma M).conjBy a
  have hKg_le_Ma : Kg ≤ M.conjBy a := by
    intro y hy
    change y ∈ (section10Msigma M).conjBy a at hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    have hzM : z ∈ M := section14_msigma_le M hz
    exact Subgroup.mem_map.mpr ⟨z, hzM, by simp [MulAut.conj_apply]⟩
  have hKg_norm : (Kg.subgroupOf (M.conjBy a)).Normal := by
    let e : M ≃* M.conjBy a := (MulAut.conj a).subgroupMap M
    rw [section14_msigma_conjBy_subgroupOf (G := G) M a]
    exact Subgroup.Normal.map
      (piCore_normal (G := M) (π := section10SigmaPrimes M)) e.toMonoidHom e.surjective
  have hKg_pi_M : IsPiSubgroup (G := G) (section10SigmaPrimes M) Kg := by
    have hMsigma_pi :
        IsPiSubgroup (G := G) (section10SigmaPrimes M) (section10Msigma M) := by
      change IsPiSubgroup (G := G) (section10SigmaPrimes M)
        (piCoreIn (section10SigmaPrimes M) M)
      exact piCoreIn_isPiSubgroup (G := G) (π := section10SigmaPrimes M) M
    intro p hpKg
    have hpMσ : p.val ∣ Nat.card (section10Msigma M) := by
      have hcard :
          Nat.card Kg = Nat.card (section10Msigma M) := by
        simpa [Kg, Subgroup.conjBy] using
          (Subgroup.card_map_of_injective
            (K := section10Msigma M) (f := (MulAut.conj a).toMonoidHom)
            (MulAut.conj a).injective)
      simpa [hcard] using hpKg
    exact hMsigma_pi p hpMσ
  have hKg_pi : IsPiSubgroup (G := G) (section10SigmaPrimes (M.conjBy a)) Kg := by
    intro p hpKg
    exact section14_sigma_mem_conjBy (L := M) (hKg_pi_M p hpKg) a
  have hKg_le_sigma :
      Kg ≤ section10Msigma (M.conjBy a) :=
    section8_le_piCoreIn_of_normal_isPiSubgroup
      (G := G) (π := section10SigmaPrimes (M.conjBy a))
      hKg_le_Ma hKg_norm hKg_pi
  have hxKg : a * x * a⁻¹ ∈ Kg := by
    exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
  exact hKg_le_sigma hxKg

omit [IsMinCE G] in
public theorem CFSG.section14_msigmaElement_conjBy
    {M : Subgroup G} {x a : G} (hM : M ∈ section14MsigmaElement x) :
    M.conjBy a ∈ section14MsigmaElement (a * x * a⁻¹) := by
  refine ⟨section14_maximal_conjBy (G := G) hM.1 a, ?_⟩
  intro y hy
  rcases Set.mem_singleton_iff.mp hy with rfl
  exact section14_mem_msigma_conjBy (G := G) (M := M) (x := x) (a := a) (hM.2 (by simp))

omit [IsMinCE G] in
public theorem CFSG.section14_msigma_conjBy
    (M : Subgroup G) (a : G) :
    (section10Msigma M).conjBy a = section10Msigma (M.conjBy a) := by
  ext y
  constructor
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact section14_mem_msigma_conjBy (G := G) (M := M) (x := x) (a := a) hx
  · intro hy
    have hyBack :=
      section14_mem_msigma_conjBy (G := G) (M := M.conjBy a) (x := y) (a := a⁻¹) hy
    have hyM : a⁻¹ * y * a ∈ section10Msigma M := by
      simpa [section11_conjBy_inv, mul_assoc] using hyBack
    exact Subgroup.mem_map.mpr ⟨a⁻¹ * y * a, hyM, by simp [MulAut.conj_apply, mul_assoc]⟩

private noncomputable def CFSG.section14_msigmaElement_conjEquiv
    (x a : G) :
    {M : Subgroup G // M ∈ section14MsigmaElement x} ≃
      {L : Subgroup G // L ∈ section14MsigmaElement (a * x * a⁻¹)} := by
  refine
    { toFun := fun M => ⟨M.1.conjBy a, section14_msigmaElement_conjBy (G := G) M.2⟩
      invFun := fun L => ⟨L.1.conjBy a⁻¹, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hback :=
      section14_msigmaElement_conjBy (G := G) (x := a * x * a⁻¹) (a := a⁻¹) L.2
    simpa [section11_conjBy_inv, mul_assoc] using hback
  · intro M
    apply Subtype.ext
    exact section11_conjBy_inv (G := G) M.1 a
  · intro L
    apply Subtype.ext
    exact section11_conjBy_inv' (G := G) L.1 a

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_elementCentralizerIn_conjBy
    (H : Subgroup G) (x a : G) :
    (elementCentralizerIn H x).conjBy a =
      elementCentralizerIn (H.conjBy a) (a * x * a⁻¹) := by
  ext y
  constructor
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨z, hz.1, by simp [MulAut.conj_apply]⟩
    · have hzcomm : Commute z x := Subgroup.mem_centralizer_singleton_iff.mp hz.2
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      change (a * z * a⁻¹) * (a * x * a⁻¹) = (a * x * a⁻¹) * (a * z * a⁻¹)
      have hmul := congrArg (fun t : G => a * t * a⁻¹) hzcomm.eq
      simpa [mul_assoc] using hmul
  · intro hy
    refine Subgroup.mem_map.mpr ⟨a⁻¹ * y * a, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    refine ⟨?_, ?_⟩
    · rcases hy.1 with ⟨z, hz, hzy⟩
      have hzy' : a * z * a⁻¹ = y := by
        simpa [MulAut.conj_apply] using hzy
      have hzEq : z = a⁻¹ * y * a := by
        calc
          z = a⁻¹ * (a * z * a⁻¹) * a := by simp [mul_assoc]
          _ = a⁻¹ * y * a := by rw [hzy']
      simpa [hzEq] using hz
    · have hycomm : Commute y (a * x * a⁻¹) := Subgroup.mem_centralizer_singleton_iff.mp hy.2
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hmul := congrArg (fun t : G => a⁻¹ * t * a) hycomm.eq
      simpa [mul_assoc] using hmul

private theorem CFSG.section14_N_conjBy_of_nonsingleton
    {x a : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x}) :
    section14N (a * x * a⁻¹) = (section14N x).conjBy a := by
  classical
  have hx' : a * x * a⁻¹ ≠ 1 := by
    intro h1
    apply hx
    have hconj := congrArg (fun t : G => a⁻¹ * t * a) h1
    simpa [mul_assoc] using hconj
  have hσ' : (section14MsigmaElement (a * x * a⁻¹)).Nonempty := by
    rcases hσ with ⟨M, hM⟩
    exact ⟨M.conjBy a, section14_msigmaElement_conjBy (G := G) hM⟩
  have hcard_eq :
      Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x} =
        Nat.card {L : Subgroup G // L ∈ section14MsigmaElement (a * x * a⁻¹)} :=
    Nat.card_congr (section14_msigmaElement_conjEquiv (G := G) x a)
  have hcard' : 1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement (a * x * a⁻¹)} := by
    rw [← hcard_eq]
    exact hcard
  have hNx' :
      section14N (a * x * a⁻¹) ∈
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({a * x * a⁻¹} : Set G)) :=
    section14N_mem_of_nonsingleton (G := G) hx' hσ' hcard'
  have hNxconj :
      (section14N x).conjBy a ∈
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({a * x * a⁻¹} : Set G)) := by
    refine ⟨section14_maximal_conjBy (G := G)
      (section14N_mem_of_nonsingleton (G := G) hx hσ hcard).1 a, ?_⟩
    intro y hy
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨a⁻¹ * y * a, ?_, by simp [mul_assoc]⟩
    have hycomm : Commute y (a * x * a⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp hy
    have hcomm : Commute (a⁻¹ * y * a) x := by
      change (a⁻¹ * y * a) * x = x * (a⁻¹ * y * a)
      have hmul := congrArg (fun t : G => a⁻¹ * t * a) hycomm.eq
      simpa [mul_assoc] using hmul
    exact
      (section14N_mem_of_nonsingleton (G := G) hx hσ hcard).2
        (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  obtain ⟨N0, _hN0, huniqN0⟩ :=
    theorem_14_4_unique_N (G := G) (x := a * x * a⁻¹) hx' hσ' hcard'
  have hchoice_eq : section14N (a * x * a⁻¹) = N0 := huniqN0 _ hNx'
  have hconj_eq : (section14N x).conjBy a = N0 := huniqN0 _ hNxconj
  exact hchoice_eq.trans hconj_eq.symm

private theorem CFSG.section14_R_conjBy_of_nonsingleton
    {x a : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x}) :
    (section14R x).conjBy a = section14R (a * x * a⁻¹) := by
  classical
  have hx' : a * x * a⁻¹ ≠ 1 := by
    intro h1
    apply hx
    have hconj := congrArg (fun t : G => a⁻¹ * t * a) h1
    simpa [mul_assoc] using hconj
  have hσ' : (section14MsigmaElement (a * x * a⁻¹)).Nonempty := by
    rcases hσ with ⟨M, hM⟩
    exact ⟨M.conjBy a, section14_msigmaElement_conjBy (G := G) hM⟩
  have hcard_eq :
      Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x} =
        Nat.card {L : Subgroup G // L ∈ section14MsigmaElement (a * x * a⁻¹)} :=
    Nat.card_congr (section14_msigmaElement_conjEquiv (G := G) x a)
  have hcard' : 1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement (a * x * a⁻¹)} := by
    rw [← hcard_eq]
    exact hcard
  let M : Subgroup G := Classical.choose hσ
  have hM : M ∈ section14MsigmaElement x := Classical.choose_spec hσ
  let M' : Subgroup G := Classical.choose hσ'
  have hM' : M' ∈ section14MsigmaElement (a * x * a⁻¹) := Classical.choose_spec hσ'
  have hRdef :
      section14R x =
        elementCentralizerIn (section10Msigma (section14N x)) x :=
    (theorem_14_4_a (G := G) (x := x) hx hσ hcard hM).1
  have hRdef' :
      section14R (a * x * a⁻¹) =
        elementCentralizerIn
          (section10Msigma (section14N (a * x * a⁻¹))) (a * x * a⁻¹) :=
    (theorem_14_4_a (G := G) (x := a * x * a⁻¹) hx' hσ' hcard' hM').1
  rw [hRdef, hRdef', section14_N_conjBy_of_nonsingleton (G := G) hx hσ hcard]
  simpa [section14_msigma_conjBy (G := G) (section14N x) a] using
    (section14_elementCentralizerIn_conjBy (G := G)
      (section10Msigma (section14N x)) x a)

public theorem CFSG.section14_mem_tilde_conjBy
    {M : Subgroup G} {g a : G} (hg : g ∈ section14Tilde M) :
    a⁻¹ * g * a ∈ section14Tilde (M.conjBy a⁻¹) := by
  rcases hg with ⟨x, hxMσ, hxne, r, hr, rfl⟩
  refine ⟨a⁻¹ * x * a, ?_, ?_, a⁻¹ * r * a, ?_, ?_⟩
  · simpa using
      (section14_mem_msigma_conjBy (G := G) (M := M) (x := x) (a := a⁻¹) hxMσ)
  · intro h1
    apply hxne
    have hconj := congrArg (fun t : G => a * t * a⁻¹) h1
    simpa [mul_assoc] using hconj
  · by_cases hr1 : r = 1
    · simp [hr1]
    · obtain ⟨hx, hσx, hcardx⟩ :=
        section14_nonsingleton_of_mem_R_ne_one (G := G) hr hr1
      have hrConj :
          a⁻¹ * r * a ∈ (section14R x).conjBy a⁻¹ := by
        exact Subgroup.mem_map.mpr ⟨r, hr, by simp⟩
      simpa [section14_R_conjBy_of_nonsingleton (G := G) (a := a⁻¹) hx hσx hcardx,
        mul_assoc] using hrConj
  · simp [mul_assoc]

private theorem CFSG.section14_tilde_setConjBy
    (M : Subgroup G) (a : G) :
    section14SetConjBy (section14Tilde M) a = section14Tilde (M.conjBy a⁻¹) := by
  ext g
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact section14_mem_tilde_conjBy (G := G) (M := M) (g := t) (a := a) ht
  · intro hg
    refine ⟨a * g * a⁻¹, ?_, by simp [mul_assoc]⟩
    simpa [section11_conjBy_inv', mul_assoc] using
      (section14_mem_tilde_conjBy (G := G) (M := M.conjBy a⁻¹) (g := g) (a := a⁻¹) hg)

private theorem CFSG.section14_sigmaLength_one_of_mem_conjClosureMsigma
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {g : G}
    (hg :
      g ∈ section14ConjugacyClosure
        {y | y ∈ section10Msigma M ∧ y ≠ 1}) :
    section14SigmaLength g = 1 := by
  rcases hg with ⟨y, hy, a, rfl⟩
  rcases hy with ⟨hyMσ, hyne⟩
  have hgMσ : a⁻¹ * y * a ∈ section10Msigma (M.conjBy a⁻¹) := by
    simpa using
      (section14_mem_msigma_conjBy (G := G) (M := M) (x := y) (a := a⁻¹) hyMσ)
  have hMga : M.conjBy a⁻¹ ∈ section9MaximalSubgroups G :=
    section14_maximal_conjBy (G := G) hM a⁻¹
  have hgne : a⁻¹ * y * a ≠ 1 := by
    intro h1
    apply hyne
    have hconj := congrArg (fun t : G => a * t * a⁻¹) h1
    simpa [mul_assoc] using hconj
  exact section14_sigmaLength_one_of_mem_msigma (G := G) hMga hgMσ hgne

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_conjugateSubgroups_trans
    {A B C : Subgroup G}
    (hAB : section14ConjugateSubgroups A B)
    (hBC : section14ConjugateSubgroups B C) :
    section14ConjugateSubgroups A C := by
  rcases hAB with ⟨a, rfl⟩
  rcases hBC with ⟨b, rfl⟩
  exact ⟨a * b, by
    simpa using (section11_conjBy_conjBy (G := G) C b a)⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_maximal_of_conjugate
    {M L : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hLM : section14ConjugateSubgroups L M) :
    L ∈ section9MaximalSubgroups G := by
  rcases hLM with ⟨a, hLa⟩
  rw [hLa]
  exact section14_maximal_conjBy (G := G) hM a

public def CFSG.section14ConjClosureMsigmaNonid (M : Subgroup G) : Set G :=
  section14ConjugacyClosure {y | y ∈ section10Msigma M ∧ y ≠ 1}

omit [IsMinCE G] in
public theorem CFSG.section14_mem_conjClosureMsigmaNonid_of_mem_msigma_of_conjugate
    {M L : Subgroup G} (hLM : section14ConjugateSubgroups L M)
    {x : G} (hxLσ : x ∈ section10Msigma L) (hxne : x ≠ 1) :
    x ∈ section14ConjClosureMsigmaNonid M := by
  rcases hLM with ⟨a, hLa⟩
  rw [section14ConjClosureMsigmaNonid]
  rw [hLa, ← section14_msigma_conjBy (G := G) M a] at hxLσ
  rcases Subgroup.mem_map.mp hxLσ with ⟨y, hyMσ, hxy⟩
  refine ⟨y, ⟨hyMσ, ?_⟩, a⁻¹, ?_⟩
  · intro hy1
    apply hxne
    rw [← hxy, hy1]
    simp
  · simpa [MulAut.conj_apply] using hxy.symm

omit [IsMinCE G] in
private theorem CFSG.section14_msigmaElement_nonempty_of_mem_conjClosureMsigmaNonid
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {x : G} (hx : x ∈ section14ConjClosureMsigmaNonid M) :
    (section14MsigmaElement x).Nonempty := by
  rcases hx with ⟨y, ⟨hyMσ, hyne⟩, a, hxy⟩
  refine ⟨M.conjBy a⁻¹, ?_⟩
  refine ⟨section14_maximal_conjBy (G := G) hM a⁻¹, ?_⟩
  intro z hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  simpa [hxy] using
    (section14_mem_msigma_conjBy (G := G) (M := M) (x := y) (a := a⁻¹) hyMσ)

private theorem CFSG.section14_conjugate_of_mem_msigmaElement_of_mem_conjClosureMsigmaNonid
    {M L : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {x : G} (hx : x ∈ section14ConjClosureMsigmaNonid M)
    (hLx : L ∈ section14MsigmaElement x) :
    section14ConjugateSubgroups L M := by
  rcases hx with ⟨y, ⟨hyMσ, hyne⟩, a, hxy⟩
  let L₀ : Subgroup G := M.conjBy a⁻¹
  have hL₀max : L₀ ∈ section9MaximalSubgroups G :=
    section14_maximal_conjBy (G := G) hM a⁻¹
  have hxL₀σ : x ∈ section10Msigma L₀ := by
    simpa [L₀, hxy] using
      (section14_mem_msigma_conjBy (G := G) (M := M) (x := y) (a := a⁻¹) hyMσ)
  have hL₀x : L₀ ∈ section14MsigmaElement x := by
    refine ⟨hL₀max, ?_⟩
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hxL₀σ
  have hxne : x ≠ 1 := by
    intro hx1
    apply hyne
    have hconj := congrArg (fun t : G => a * t * a⁻¹) hx1
    simpa [hxy, mul_assoc] using hconj
  have hL₀M : section14ConjugateSubgroups L₀ M := ⟨a⁻¹, rfl⟩
  by_contra hnotLM
  have hnotLL₀ : ¬ section14ConjugateSubgroups L L₀ := by
    intro hLL₀
    exact hnotLM (section14_conjugateSubgroups_trans (G := G) hLL₀ hL₀M)
  have hxTildeL : x ∈ section14Tilde L := by
    refine ⟨x, hLx.2 (by simp), hxne, 1, (section14R x).one_mem, by simp⟩
  have hxTildeL₀ : x ∈ section14Tilde L₀ := by
    refine ⟨x, hxL₀σ, hxne, 1, (section14R x).one_mem, by simp⟩
  exact
    (Set.eq_empty_iff_forall_notMem.mp
      (lemma_14_5_b (G := G) hL₀max hLx.1 hnotLL₀))
      x ⟨hxTildeL, hxTildeL₀⟩

public theorem CFSG.section14_maximal_normalizer_eq_self_of_msigma_member
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {x : G} (hxMσ : x ∈ section10Msigma M) (hxne : x ≠ 1) :
    Subgroup.normalizer (M : Set G) = M := by
  obtain ⟨q, z, _hz_zpowx, _hzMσ, _hz_ne, hzprime⟩ :=
    section14_exists_primeOrder_zpowers_in (G := G)
      (B := section10Msigma M) hxMσ hxne
  have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
    rw [subgroupPrimeSet]
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
      ⟨_hzle, hqcard⟩
    simp [hqcard]
  have hqMσ : q ∈ subgroupPrimeSet (section10Msigma M) := by
    exact section8_subgroupPrimeSet_mono
      (Subgroup.zpowers_le.2 (by
        rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
          ⟨hzle, _hqcard⟩
        exact hzle))
      hqz
  have hqM : q ∈ subgroupPrimeSet M :=
    section8_subgroupPrimeSet_mono
      (section14_msigma_le M) hqMσ
  apply le_antisymm
  · have hnorm_proper : Subgroup.normalizer (M : Set G) ≠ ⊤ := by
      intro hnorm_top
      have hMnormal : M.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
      letI : IsSimpleGroup G := IsMinCE.simple
      rcases (haveI := hMnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal M) with hMbot | hMtop
      · rw [subgroupPrimeSet] at hqM
        have hq_one : q.val ∣ 1 := by simpa [hMbot] using hqM
        exact q.2.not_dvd_one hq_one
      · exact hM.1 hMtop
    exact le_of_eq ((hM.le_iff_eq hnorm_proper).mp Subgroup.le_normalizer)
  · exact Subgroup.le_normalizer

private noncomputable def CFSG.section14_msigmaNonidEquiv_of_conjugate
    {M L : Subgroup G} (hLM : section14ConjugateSubgroups L M) :
    {x : G // x ∈ section10Msigma L ∧ x ≠ 1} ≃
      {y : G // y ∈ section10Msigma M ∧ y ≠ 1} := by
  classical
  let a : G := Classical.choose hLM
  have hLa : L = M.conjBy a := Classical.choose_spec hLM
  refine
    { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
  · intro x
    refine ⟨a⁻¹ * x.1 * a, ?_, ?_⟩
    · have hx' : x.1 ∈ section10Msigma (M.conjBy a) := by
        simpa [hLa] using x.2.1
      simpa [hLa, section11_conjBy_inv, mul_assoc] using
        (section14_mem_msigma_conjBy (G := G)
          (M := M.conjBy a) (x := x.1) (a := a⁻¹) hx')
    · intro hx1
      apply x.2.2
      have hconj := congrArg (fun t : G => a * t * a⁻¹) hx1
      simpa [mul_assoc] using hconj
  · intro y
    refine ⟨a * y.1 * a⁻¹, ?_, ?_⟩
    · simpa [hLa, mul_assoc] using
        (section14_mem_msigma_conjBy (G := G) (M := M) (x := y.1) (a := a) y.2.1)
    · intro hy1
      apply y.2.2
      have hconj := congrArg (fun t : G => a⁻¹ * t * a) hy1
      simpa [mul_assoc] using hconj
  · intro x
    apply Subtype.ext
    simp [mul_assoc]
  · intro y
    apply Subtype.ext
    simp [mul_assoc]

public theorem CFSG.section14_mul_mem_conjClosureTilde_of_mem_conjClosureMsigmaNonid
    {M : Subgroup G} {x r : G}
    (hx : x ∈ section14ConjClosureMsigmaNonid M)
    (hr : r ∈ section14R x) :
    x * r ∈ section14ConjugacyClosure (section14Tilde M) := by
  rcases hx with ⟨y, ⟨hyMσ, hyne⟩, a, hxy⟩
  have hxσ : x ∈ section10Msigma (M.conjBy a⁻¹) := by
    simpa [hxy] using
      (section14_mem_msigma_conjBy (G := G) (M := M) (x := y) (a := a⁻¹) hyMσ)
  have hxne : x ≠ 1 := by
    intro hx1
    apply hyne
    have hconj := congrArg (fun t : G => a * t * a⁻¹) hx1
    simpa [hxy, mul_assoc] using hconj
  have hxr_tilde : x * r ∈ section14Tilde (M.conjBy a⁻¹) := by
    exact ⟨x, hxσ, hxne, r, hr, rfl⟩
  have hxr_setConj :
      x * r ∈ section14SetConjBy (section14Tilde M) a := by
    simpa [section14_tilde_setConjBy (G := G) M a] using hxr_tilde
  rcases hxr_setConj with ⟨t, ht, hEq⟩
  exact ⟨t, ht, a, hEq⟩

private theorem CFSG.section14_exists_factor_of_mem_conjClosureTilde
    {M : Subgroup G} {g : G}
    (hg : g ∈ section14ConjugacyClosure (section14Tilde M)) :
    ∃ x : G, x ∈ section14ConjClosureMsigmaNonid M ∧
      ∃ r ∈ section14R x, g = x * r := by
  rcases hg with ⟨t, ht, a, rfl⟩
  have ht' :
      a⁻¹ * t * a ∈ section14Tilde (M.conjBy a⁻¹) :=
    section14_mem_tilde_conjBy (G := G) (M := M) (g := t) (a := a) ht
  rcases ht' with ⟨x, hxσ, hxne, r, hr, hEq⟩
  refine ⟨x, ?_, r, hr, hEq⟩
  exact
    section14_mem_conjClosureMsigmaNonid_of_mem_msigma_of_conjugate
      (G := G) (M := M) (L := M.conjBy a⁻¹) ⟨a⁻¹, rfl⟩ hxσ hxne

public theorem CFSG.section14_conjClosure_tilde_disjoint_of_not_conjugate
    {M₁ M₂ : Subgroup G}
    (hM₁ : M₁ ∈ section9MaximalSubgroups G)
    (hM₂ : M₂ ∈ section9MaximalSubgroups G)
    (hnotconj : ¬ section14ConjugateSubgroups M₂ M₁) :
    section14ConjugacyClosure (section14Tilde M₂) ∩
      section14ConjugacyClosure (section14Tilde M₁) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro g hg
  rcases hg with ⟨hg₂, hg₁⟩
  rcases section14_exists_factor_of_mem_conjClosureTilde
      (G := G) (M := M₂) hg₂ with ⟨x₂, hx₂, r₂, hr₂, hgEq₂⟩
  rcases section14_exists_factor_of_mem_conjClosureTilde
      (G := G) (M := M₁) hg₁ with ⟨x₁, hx₁, r₁, hr₁, hgEq₁⟩
  have hx₂len : section14SigmaLength x₂ = 1 :=
    section14_sigmaLength_one_of_mem_conjClosureMsigma (G := G) hM₂ hx₂
  have hx₁len : section14SigmaLength x₁ = 1 :=
    section14_sigmaLength_one_of_mem_conjClosureMsigma (G := G) hM₁ hx₁
  by_cases hxx : x₂ = x₁
  · subst hxx
    have hσ : (section14MsigmaElement x₂).Nonempty :=
      section14_msigmaElement_nonempty_of_mem_conjClosureMsigmaNonid
        (G := G) hM₁ hx₁
    let L : Subgroup G := Classical.choose hσ
    have hL : L ∈ section14MsigmaElement x₂ := Classical.choose_spec hσ
    have hLM₂ :
        section14ConjugateSubgroups L M₂ :=
      section14_conjugate_of_mem_msigmaElement_of_mem_conjClosureMsigmaNonid
        (G := G) hM₂ (by simpa using hx₂) hL
    have hLM₁ :
        section14ConjugateSubgroups L M₁ :=
      section14_conjugate_of_mem_msigmaElement_of_mem_conjClosureMsigmaNonid
        (G := G) hM₁ hx₁ hL
    rcases hLM₂ with ⟨a, hLa⟩
    rcases hLM₁ with ⟨b, hLb⟩
    have hM₂M₁ : section14ConjugateSubgroups M₂ M₁ := by
      refine ⟨a⁻¹ * b, ?_⟩
      calc
        M₂ = (M₂.conjBy a).conjBy a⁻¹ := (section11_conjBy_inv (G := G) M₂ a).symm
        _ = L.conjBy a⁻¹ := by rw [hLa]
        _ = (M₁.conjBy b).conjBy a⁻¹ := by rw [hLb]
        _ = M₁.conjBy (a⁻¹ * b) := by rw [section11_conjBy_conjBy]
    exact hnotconj hM₂M₁
  · have hgCoset :
        g ∈ section14ElementCoset x₂ (section14R x₂) ∩
          section14ElementCoset x₁ (section14R x₁) := by
      refine ⟨⟨r₂, hr₂, hgEq₂⟩, ⟨r₁, hr₁, hgEq₁⟩⟩
    exact
      (Set.eq_empty_iff_forall_notMem.mp
        (lemma_14_5_a (G := G) (x := x₂) (y := x₁) hx₂len hx₁len hxx))
        g hgCoset

public theorem CFSG.section14_conjClosure_tilde_disjoint_of_not_conjugate_public
    {M₁ M₂ : Subgroup G}
    (hM₁ : M₁ ∈ section9MaximalSubgroups G)
    (hM₂ : M₂ ∈ section9MaximalSubgroups G)
    (hnotconj : ¬ section14ConjugateSubgroups M₂ M₁) :
    section14ConjugacyClosure (section14Tilde M₂) ∩
      section14ConjugacyClosure (section14Tilde M₁) = ∅ :=
  section14_conjClosure_tilde_disjoint_of_not_conjugate
    (G := G) hM₁ hM₂ hnotconj

private noncomputable def CFSG.section14_R_equiv_msigmaElement_of_mem_conjClosureMsigmaNonid
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {x : G} (hx : x ∈ section14ConjClosureMsigmaNonid M) :
    section14R x ≃ {L : Subgroup G // L ∈ section14MsigmaElement x} := by
  classical
  have hσ : (section14MsigmaElement x).Nonempty :=
    section14_msigmaElement_nonempty_of_mem_conjClosureMsigmaNonid (G := G) hM hx
  have hxlen : section14SigmaLength x = 1 :=
    section14_sigmaLength_one_of_mem_conjClosureMsigma (G := G) hM hx
  have hxne : x ≠ 1 := section14_sigmaLength_one_ne_one hxlen
  let Mx : Subgroup G := Classical.choose hσ
  have hMx : Mx ∈ section14MsigmaElement x := Classical.choose_spec hσ
  have hSharp :
      section14SharpTransitiveOn (section14R x) (section14MsigmaElement x) :=
    (theorem_14_4 (G := G) (x := x) hxne hσ).2.1
  have hRleCx : section14R x ≤ Subgroup.centralizer ({x} : Set G) :=
    Classical.choose ((theorem_14_4 (G := G) (x := x) hxne hσ).1)
  let f : section14R x → {L : Subgroup G // L ∈ section14MsigmaElement x} := fun r =>
    ⟨Mx.conjBy (r : G), by
      refine ⟨section14_maximal_conjBy (G := G) hMx.1 (r : G), ?_⟩
      have hxMxσ : x ∈ section10Msigma Mx := hMx.2 (by simp)
      have hxConj :
          (r : G) * x * (r : G)⁻¹ ∈ section10Msigma (Mx.conjBy (r : G)) :=
        section14_mem_msigma_conjBy (G := G) (M := Mx) (x := x) (a := (r : G)) hxMxσ
      have hrcomm : Commute (r : G) x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hRleCx r.property)
      simpa [Set.singleton_subset_iff, hrcomm.eq, mul_assoc] using hxConj⟩
  have hfBij : Function.Bijective f := by
    rw [Function.bijective_iff_existsUnique]
    intro L
    rcases hSharp Mx hMx L.1 L.2 with ⟨r, hr, huniq⟩
    refine ⟨r, ?_, ?_⟩
    · apply Subtype.ext
      simpa using hr.symm
    · intro r' hr'
      have hval : L.1 = Mx.conjBy (r' : G) := by
        simpa using (congrArg Subtype.val hr').symm
      exact huniq r' hval
  exact Equiv.ofBijective f hfBij

/-- Lemma 14.5(c): cardinality of the conjugacy closure of `M̃`. -/
public theorem CFSG.lemma_14_5_c
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    Nat.card (section14ConjugacyClosure (section14Tilde M)) =
      (Nat.card (section10Msigma M) - 1) * M.index := by
  classical
  by_cases hσbot : section10Msigma M = ⊥
  · have htilde : section14Tilde M = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro g hg
      rcases hg with ⟨x, hxMσ, hxne, r, _hr, rfl⟩
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        simpa [hσbot] using hxMσ
      exact hxne (by simpa using hxbot)
    have hclosure : section14ConjugacyClosure (section14Tilde M) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro g hg
      rcases hg with ⟨t, ht, _a, _hEq⟩
      exact (Set.eq_empty_iff_forall_notMem.mp htilde) t ht
    simp [hclosure, hσbot]
  · obtain ⟨x₀, hx₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hσbot
    have hx₀Mσ : (x₀ : G) ∈ section10Msigma M := x₀.property
    have hx₀ne' : (x₀ : G) ≠ 1 := by
      intro hx₀1
      apply hx₀ne
      apply Subtype.ext
      simpa using hx₀1
    have hMnorm :
        Subgroup.normalizer (M : Set G) = M :=
      section14_maximal_normalizer_eq_self_of_msigma_member
        (G := G) hM hx₀Mσ hx₀ne'
    let Ω := {x : G // x ∈ section14ConjClosureMsigmaNonid M}
    let Conjs := {L : Subgroup G // section14ConjugateSubgroups L M}
    let X0 := {x : G // x ∈ section10Msigma M ∧ x ≠ 1}
    have hClosureCard :
        Nat.card (section14ConjugacyClosure (section14Tilde M)) =
          Nat.card (Σ x : Ω, section14R x.1) := by
      let f :
          (Σ x : Ω, section14R x.1) →
            {g : G // g ∈ section14ConjugacyClosure (section14Tilde M)} := fun xr =>
          ⟨xr.1.1 * xr.2.1,
            section14_mul_mem_conjClosureTilde_of_mem_conjClosureMsigmaNonid
              (G := G) (M := M) (x := xr.1.1) (r := xr.2.1) xr.1.2 xr.2.2⟩
      have hfBij : Function.Bijective f := by
        constructor
        · intro a b hab
          rcases a with ⟨x₁, r₁⟩
          rcases b with ⟨x₂, r₂⟩
          have hEq : x₁.1 * r₁ = x₂.1 * r₂ := congrArg Subtype.val hab
          have hx₁len : section14SigmaLength x₁.1 = 1 :=
            section14_sigmaLength_one_of_mem_conjClosureMsigma (G := G) hM x₁.2
          have hx₂len : section14SigmaLength x₂.1 = 1 :=
            section14_sigmaLength_one_of_mem_conjClosureMsigma (G := G) hM x₂.2
          by_cases hxx : x₁.1 = x₂.1
          · have hxSub : x₁ = x₂ := Subtype.ext hxx
            subst hxSub
            have hrSub : r₁ = r₂ := by
              apply Subtype.ext
              have hcancel := congrArg (fun t : G => x₁.1⁻¹ * t) hEq
              simpa [mul_assoc] using hcancel
            subst hrSub
            rfl
          · have hCoset :
              x₁.1 * r₁ ∈ section14ElementCoset x₁.1 (section14R x₁.1) ∩
                section14ElementCoset x₂.1 (section14R x₂.1) := by
              refine ⟨⟨r₁, r₁.property, rfl⟩, ?_⟩
              exact ⟨r₂, r₂.property, hEq⟩
            exact False.elim <|
              (Set.eq_empty_iff_forall_notMem.mp
                (lemma_14_5_a (G := G) (x := x₁.1) (y := x₂.1)
                  hx₁len hx₂len hxx))
                (x₁.1 * r₁) hCoset
        · intro g
          rcases section14_exists_factor_of_mem_conjClosureTilde
              (G := G) (M := M) g.2 with ⟨x, hx, r, hr, hEq⟩
          refine ⟨⟨⟨x, hx⟩, ⟨r, hr⟩⟩, ?_⟩
          apply Subtype.ext
          exact hEq.symm
      exact Nat.card_congr (Equiv.ofBijective f hfBij).symm
    have hRMsigmaCard :
        Nat.card (Σ x : Ω, section14R x.1) =
          Nat.card (Σ x : Ω, {L : Subgroup G // L ∈ section14MsigmaElement x.1}) := by
      exact Nat.card_congr <|
        Equiv.sigmaCongrRight fun x =>
          section14_R_equiv_msigmaElement_of_mem_conjClosureMsigmaNonid
            (G := G) hM x.2
    have hSwapCard :
        Nat.card (Σ x : Ω, {L : Subgroup G // L ∈ section14MsigmaElement x.1}) =
          Nat.card (Σ C : Conjs, {x : G // x ∈ section10Msigma C.1 ∧ x ≠ 1}) := by
      let f :
          (Σ x : Ω, {L : Subgroup G // L ∈ section14MsigmaElement x.1}) →
            Σ C : Conjs, {x : G // x ∈ section10Msigma C.1 ∧ x ≠ 1} := fun p =>
          let hxne : p.1.1 ≠ 1 :=
            section14_sigmaLength_one_ne_one
              (section14_sigmaLength_one_of_mem_conjClosureMsigma (G := G) hM p.1.2)
          ⟨⟨p.2.1,
              section14_conjugate_of_mem_msigmaElement_of_mem_conjClosureMsigmaNonid
                (G := G) hM p.1.2 p.2.2⟩,
            ⟨p.1.1, p.2.2.2 (by simp), hxne⟩⟩
      have hfBij : Function.Bijective f := by
        constructor
        · intro a b hab
          rcases a with ⟨x₁, L₁⟩
          rcases b with ⟨x₂, L₂⟩
          have hx : x₁.1 = x₂.1 := by
            simpa [f] using congrArg (fun z => z.2.1) hab
          have hxSub : x₁ = x₂ := Subtype.ext hx
          subst hxSub
          have hL : L₁.1 = L₂.1 := by
            simpa [f] using congrArg (fun z => z.1.1) hab
          have hLSub : L₁ = L₂ := Subtype.ext hL
          subst hLSub
          rfl
        · intro c
          rcases c with ⟨C, x⟩
          have hxΩ : x.1 ∈ section14ConjClosureMsigmaNonid M :=
            section14_mem_conjClosureMsigmaNonid_of_mem_msigma_of_conjugate
              (G := G) (M := M) (L := C.1) C.2 x.2.1 x.2.2
          let p :
              (Σ x : Ω, {L : Subgroup G // L ∈ section14MsigmaElement x.1}) :=
            ⟨⟨x.1, hxΩ⟩, ⟨C.1, ⟨section14_maximal_of_conjugate (G := G) hM C.2, by
              intro y hy
              rcases Set.mem_singleton_iff.mp hy with rfl
              exact x.2.1⟩⟩⟩
          refine ⟨p, ?_⟩
          have hC : (f p).1 = C := by
            apply Subtype.ext
            rfl
          refine Sigma.ext hC ?_
          cases hC
          exact heq_of_eq <| by
            apply Subtype.ext
            rfl
      exact Nat.card_congr (Equiv.ofBijective f hfBij)
    have hT3ProdCard :
        Nat.card (Σ C : Conjs, {x : G // x ∈ section10Msigma C.1 ∧ x ≠ 1}) =
          Nat.card (Conjs × X0) := by
      exact Nat.card_congr <|
        (Equiv.sigmaCongrRight fun C =>
          section14_msigmaNonidEquiv_of_conjugate (G := G) C.2).trans
            (Equiv.sigmaEquivProd Conjs X0)
    have hConjsCard : Nat.card Conjs = M.index := by
      let e :
          (G ⧸ M) ≃ Conjs := by
        let f : (G ⧸ M) → Conjs := fun q =>
          ⟨M.conjBy (Quotient.out q), ⟨Quotient.out q, rfl⟩⟩
        have hfBij : Function.Bijective f := by
          constructor
          · intro q₁ q₂ hq
            have hEq :
                M.conjBy (Quotient.out q₁) = M.conjBy (Quotient.out q₂) := by
              simpa [f] using congrArg Subtype.val hq
            have hFix :
                M.conjBy ((Quotient.out q₁)⁻¹ * Quotient.out q₂) = M := by
              calc
                M.conjBy ((Quotient.out q₁)⁻¹ * Quotient.out q₂) =
                    (M.conjBy (Quotient.out q₂)).conjBy (Quotient.out q₁)⁻¹ := by
                      simpa using
                        (section11_conjBy_conjBy (G := G) M (Quotient.out q₂)
                          (Quotient.out q₁)⁻¹).symm
                _ = (M.conjBy (Quotient.out q₁)).conjBy (Quotient.out q₁)⁻¹ := by rw [hEq]
                _ = M := section11_conjBy_inv (G := G) M (Quotient.out q₁)
            have hNorm :
                ((Quotient.out q₁)⁻¹ * Quotient.out q₂) ∈
                  Subgroup.normalizer (M : Set G) :=
              section14_mem_normalizer_of_conjBy_eq (G := G) hFix
            have hMem :
                ((Quotient.out q₁)⁻¹ * Quotient.out q₂) ∈ M := by
              simpa [hMnorm] using hNorm
            have hqOut :
                (((Quotient.out q₁ : G) : G ⧸ M)) =
                  (((Quotient.out q₂ : G) : G ⧸ M)) :=
              QuotientGroup.eq.mpr hMem
            simpa [Quotient.out_eq' q₁, Quotient.out_eq' q₂] using hqOut
          · intro C
            rcases C.2 with ⟨a, hCa⟩
            let q : G ⧸ M := (a : G ⧸ M)
            have hqa : (Quotient.out q)⁻¹ * a ∈ M := by
              apply QuotientGroup.eq.mp
              simp [q]
            have hqaNorm :
                ((Quotient.out q)⁻¹ * a) ∈ Subgroup.normalizer (M : Set G) := by
              simpa [hMnorm] using (Subgroup.le_normalizer hqa)
            refine ⟨q, ?_⟩
            apply Subtype.ext
            calc
              M.conjBy (Quotient.out q) = M.conjBy a := by
                symm
                calc
                  M.conjBy a =
                      (M.conjBy ((Quotient.out q)⁻¹ * a)).conjBy (Quotient.out q) := by
                        simpa [mul_assoc] using
                          (section11_conjBy_conjBy (G := G) M
                            ((Quotient.out q)⁻¹ * a) (Quotient.out q)).symm
                  _ = M.conjBy (Quotient.out q) := by
                    rw [section11_conjBy_eq_of_mem_normalizer (H := M) hqaNorm]
              _ = C.1 := hCa.symm
        exact Equiv.ofBijective f hfBij
      calc
        Nat.card Conjs = Nat.card (G ⧸ M) := Nat.card_congr e.symm
        _ = M.index := by simpa using (M.index_eq_card).symm
    have hX0Card : Nat.card X0 = Nat.card (section10Msigma M) - 1 := by
      letI : Fintype (section10Msigma M) := Fintype.ofFinite (section10Msigma M)
      let e : X0 ≃ {x : section10Msigma M // x ≠ 1} :=
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by
              intro hx1
              exact x.2.2 (congrArg Subtype.val hx1)⟩
          invFun := fun x => ⟨x.1, x.1.property, by
              intro hx1
              apply x.2
              apply Subtype.ext
              simpa using hx1⟩
          left_inv := by
            intro x
            apply Subtype.ext
            rfl
          right_inv := by
            intro x
            apply Subtype.ext
            rfl }
      calc
        Nat.card X0 = Nat.card {x : section10Msigma M // x ≠ 1} := Nat.card_congr e
        _ = Fintype.card {x : section10Msigma M // x ≠ 1} :=
          Nat.card_eq_fintype_card (α := {x : section10Msigma M // x ≠ 1})
        _ = Fintype.card (section10Msigma M) - 1 := by
          simp
        _ = Nat.card (section10Msigma M) - 1 := by rw [Nat.card_eq_fintype_card]
    calc
      Nat.card (section14ConjugacyClosure (section14Tilde M))
          = Nat.card (Σ x : Ω, section14R x.1) := hClosureCard
      _ = Nat.card (Σ x : Ω, {L : Subgroup G // L ∈ section14MsigmaElement x.1}) :=
        hRMsigmaCard
      _ = Nat.card (Σ C : Conjs, {x : G // x ∈ section10Msigma C.1 ∧ x ≠ 1}) := hSwapCard
      _ = Nat.card (Conjs × X0) := hT3ProdCard
      _ = Nat.card Conjs * Nat.card X0 := Nat.card_prod Conjs X0
      _ = M.index * (Nat.card (section10Msigma M) - 1) := by rw [hConjsCard, hX0Card]
      _ = (Nat.card (section10Msigma M) - 1) * M.index := by rw [Nat.mul_comm]

end Section14
