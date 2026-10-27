module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_2_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_le
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    A ≤ M := by
  rcases (by simpa [section12RankTwoElementaryAbelianIn] using hA) with ⟨hAM, _hA⟩
  exact hAM

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_elementary
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G := by
  rcases (by simpa [section12RankTwoElementaryAbelianIn] using hA) with ⟨_hAM, hA⟩
  exact hA

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_subgroupOf_isPGroup
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    IsPGroup p.val (A.subgroupOf M) := by
  have hAM : A ≤ M := section12_rankTwo_le hA
  rcases section12_rankTwo_elementary hA with ⟨_hcard, hElem⟩
  let e : A.subgroupOf M ≃* A := Subgroup.subgroupOfEquivOfLe hAM
  have hAp : IsPGroup p.val A := by
    haveI : IsElementaryAbelian p.val A := hElem
    exact IsElementaryAbelian.isPGroup p.val A
  exact hAp.of_equiv e.symm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_prime_mem
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    p ∈ subgroupPrimeSet M := by
  have hAM : A ≤ M := section12_rankTwo_le hA
  rcases section12_rankTwo_elementary hA with ⟨hcard, _hElem⟩
  have hcard_sub : Nat.card (A.subgroupOf M) = Nat.card A :=
    natCard_subgroupOf_eq _ _ hAM
  have hp_dvd_A : p.val ∣ Nat.card A := by
    rw [hcard]
    exact dvd_pow_self p.val (by decide : 2 ≠ 0)
  have hp_dvd_sub : p.val ∣ Nat.card (A.subgroupOf M) := by
    simpa [hcard_sub] using hp_dvd_A
  exact hp_dvd_sub.trans (Subgroup.card_subgroup_dvd_card (A.subgroupOf M))

omit [IsMinCE G] in
public theorem CFSG.section12_pSubgroup_le_normal_hall_of_prime_mem
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    {H A : Subgroup R} [H.Normal] {p : Nat.Primes}
    (hHall : IsHallSubgroup π H) (hpπ : p ∈ π)
    (hAp : IsPGroup p.val A) :
    A ≤ H := by
  classical
  letI : Fact p.val.Prime := ⟨p.property⟩
  rw [← QuotientGroup.ker_mk' H]
  rw [← Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' H) (H := A)]
  by_contra hmap_ne_bot
  have hAmap_p : IsPGroup p.val (A.map (QuotientGroup.mk' H)) :=
    IsPGroup.map hAp (QuotientGroup.mk' H)
  obtain ⟨n, hn⟩ := hAmap_p.exists_card_eq
  have hp_dvd_map : p.val ∣ Nat.card (A.map (QuotientGroup.mk' H)) := by
    rw [hn]
    cases n with
    | zero =>
        have hcard_one : Nat.card (A.map (QuotientGroup.mk' H)) = 1 := by
          simpa [hn]
        exact False.elim
          (hmap_ne_bot
            ((Subgroup.card_eq_one (H := A.map (QuotientGroup.mk' H))).1 hcard_one))
    | succ n =>
        exact dvd_pow_self p.val (Nat.succ_ne_zero n)
  have hcard_map_dvd_quot :
      Nat.card (A.map (QuotientGroup.mk' H)) ∣ Nat.card (R ⧸ H) :=
    Subgroup.card_subgroup_dvd_card (A.map (QuotientGroup.mk' H))
  have hp_dvd_quot : p.val ∣ Nat.card (R ⧸ H) :=
    hp_dvd_map.trans hcard_map_dvd_quot
  have hp_dvd_index : p.val ∣ H.index := by
    simpa [Subgroup.index_eq_card] using hp_dvd_quot
  exact (hHall.p_in_pi_of_p_dvd_index p hp_dvd_index) hpπ

public theorem CFSG.section12_rankTwo_le_msigma_of_sigma
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∈ section10SigmaPrimes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    A ≤ section10Msigma M := by
  classical
  have hAM : A ≤ M := section12_rankTwo_le hA
  have hAsub_p : IsPGroup p.val (A.subgroupOf M) :=
    section12_rankTwo_subgroupOf_isPGroup hA
  have hAsub_le_sigmaSub : A.subgroupOf M ≤ section10MsigmaSubgroup M :=
    section12_pSubgroup_le_normal_hall_of_prime_mem
      (H := section10MsigmaSubgroup M) (A := A.subgroupOf M)
      (theorem_10_2_b (M := M) hM).2 hpσ hAsub_p
  intro x hxA
  have hxsub : (⟨x, hAM hxA⟩ : M) ∈ A.subgroupOf M := by
    simpa [Subgroup.mem_subgroupOf] using hxA
  have hxσsub : (⟨x, hAM hxA⟩ : M) ∈ section10MsigmaSubgroup M :=
    hAsub_le_sigmaSub hxsub
  have hxσsub' : (⟨x, hAM hxA⟩ : M) ∈ (section10Msigma M).subgroupOf M := by
    simpa [section12Msigma_subgroupOf_eq] using hxσsub
  simpa [Subgroup.mem_subgroupOf] using hxσsub'

public theorem CFSG.section12_exists_section11Data_of_not_sigma_pre
    {M A A₀ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∉ section10SigmaPrimes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (hNA₀ : Subgroup.normalizer (A₀ : Set G) ≤ M) :
    ∃ P : Sylow p.val M, section11Data M A₀ A p P := by
  classical
  have hAM : A ≤ M := section12_rankTwo_le hA
  have hArank : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G :=
    section12_rankTwo_elementary hA
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hA₀) with ⟨hA₀A, hA₀card⟩
  have hA₀M : A₀ ≤ M := hA₀A.trans hAM
  have hA₀inM : A₀ ∈ section10PrimeOrderSubgroupsIn p M := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hA₀M, hA₀card⟩
  have h10_5 := lemma_10_5 (G := G) hM hpσ hA₀card hNA₀
  rcases h10_5 with ⟨hprank, hideal, _hAext⟩
  have hpα : p ∉ section10AlphaPrimes M := by
    intro hpα
    exact hpσ (section12_sigmaPrimes_mem_of_alphaPrimes_mem hM hpα)
  have hAmax : A ∈ maximalElementaryAbelianSubgroups p.val G :=
    (lemma_10_4_c (G := G) hM hpσ hprank).2 hAM hArank
  have hAmaxRank : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G := by
    simpa [section10RankTwoMaximalElementaryAbelianSubgroups] using ⟨hArank, hAmax⟩
  have hAsub_p : IsPGroup p.val (A.subgroupOf M) :=
    section12_rankTwo_subgroupOf_isPGroup hA
  obtain ⟨P, hAsub_le_P⟩ := IsPGroup.exists_le_sylow (G := M) (p := p.val) hAsub_p
  have hA_le_Pamb : A ≤ section10AmbientSylowSubgroup M P := by
    intro x hxA
    have hxsub : (⟨x, hAM hxA⟩ : M) ∈ A.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hxA
    exact Subgroup.mem_map.mpr ⟨⟨x, hAM hxA⟩, hAsub_le_P hxsub, rfl⟩
  have hpM : p ∈ subgroupPrimeSet M :=
    section12_rankTwo_prime_mem hA
  have hPnorm_not : ¬ Subgroup.normalizer (section10AmbientSylowSubgroup M P : Set G) ≤ M := by
    intro hPnorm
    exact hpσ ⟨hpM, P, hPnorm⟩
  have hCentA₀M : Subgroup.centralizer (A₀ : Set G) ≤ M :=
    (centralizer_le_normalizer A₀).trans hNA₀
  have hCentA_le_CentA₀ :
      Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (A₀ : Set G) :=
    Subgroup.centralizer_le (show (A₀ : Set G) ⊆ (A : Set G) from hA₀A)
  have hCentAM : Subgroup.centralizer (A : Set G) ≤ M :=
    hCentA_le_CentA₀.trans hCentA₀M
  refine ⟨P, ?_⟩
  exact ⟨⟨hM, hpσ, hA₀inM, hNA₀⟩, hprank, hideal, hA₀A, hAM, hArank,
    hA_le_Pamb, hPnorm_not, hCentA₀M, hCentA_le_CentA₀, hCentAM, hAmaxRank⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_mono
    {H K A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p H) (hHK : H ≤ K) :
    A ∈ section12RankTwoElementaryAbelianIn p K := by
  exact ⟨(section12_rankTwo_le hA).trans hHK, section12_rankTwo_elementary hA⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_of_inf_left_pre
    {H K A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p (H ⊓ K)) :
    A ∈ section12RankTwoElementaryAbelianIn p H :=
  section12_rankTwo_mono hA inf_le_left

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_of_inf_right_pre
    {H K A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p (H ⊓ K)) :
    A ∈ section12RankTwoElementaryAbelianIn p K :=
  section12_rankTwo_mono hA inf_le_right

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_map_subtype_le_normalizer_of_normal_pre
    (K : Subgroup G) (H : Subgroup K) [H.Normal] :
    K ≤ Subgroup.normalizer (H.map K.subtype : Set G) := by
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
    · simpa using
        Subgroup.Normal.conj_mem inferInstance h hhH ((⟨k, hk⟩ : K)⁻¹)
    · calc
        ((((⟨k, hk⟩ : K)⁻¹ * h * ⟨k, hk⟩ : K) : G)) =
            k⁻¹ * ((h : K) : G) * k := by rfl
        _ = k⁻¹ * (k * x * k⁻¹) * k := by
          have hhx' : (h : G) = k * x * k⁻¹ := hhx
          rw [hhx']
        _ = x := by simp [mul_assoc]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_le_normalizer_msigma {M : Subgroup G} :
    M ≤ Subgroup.normalizer (section10Msigma M : Set G) := by
  simpa [section10Msigma] using
    section12_map_subtype_le_normalizer_of_normal_pre M (section10MsigmaSubgroup M)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_le_normalizer_malpha_pre {M : Subgroup G} :
    M ≤ Subgroup.normalizer (section10Malpha M : Set G) := by
  simpa [section10Malpha] using
    section12_map_subtype_le_normalizer_of_normal_pre M (section10MalphaSubgroup M)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_le_normalizer_inf_pre
    {A H K : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer (H ⊓ K : Set G) := by
  intro a ha
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hAH ha, hAK ha⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_le_normalizer_msigma_inf_pre
    {M Mstar A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p (M ⊓ Mstar)) :
    A ≤ Subgroup.normalizer (section10Msigma M ⊓ Mstar : Set G) := by
  have hAM : A ≤ M := (section12_rankTwo_le hA).trans inf_le_left
  have hAMstar : A ≤ Mstar := (section12_rankTwo_le hA).trans inf_le_right
  exact section12_le_normalizer_inf_pre
    (H := section10Msigma M) (K := Mstar)
    (hAM.trans section12_le_normalizer_msigma) (hAMstar.trans Subgroup.le_normalizer)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_rankTwo_le_normalizer_malpha_inf_pre
    {M Mstar A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p (M ⊓ Mstar)) :
    A ≤ Subgroup.normalizer (section10Malpha M ⊓ Mstar : Set G) := by
  have hAM : A ≤ M := (section12_rankTwo_le hA).trans inf_le_left
  have hAMstar : A ≤ Mstar := (section12_rankTwo_le hA).trans inf_le_right
  exact section12_le_normalizer_inf_pre
    (H := section10Malpha M) (K := Mstar)
    (hAM.trans section12_le_normalizer_malpha_pre) (hAMstar.trans Subgroup.le_normalizer)


omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_isPiSubgroup_subgroupOf_pre
    {π : Set Nat.Primes} {H K : Subgroup G}
    (hKπ : IsPiSubgroup (G := G) π K) (hKH : K ≤ H) :
    IsPiSubgroup (G := H) π (K.subgroupOf H) := by
  intro p hp
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    natCard_subgroupOf_eq _ _ hKH
  exact hKπ p (by rwa [hcard] at hp)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_isPiGroup_singleton_of_isPGroup_pre
    {R : Type*} [Group R] [Finite R] {p : Nat.Primes}
    (hR : IsPGroup p.val R) :
    IsPiGroup ({p} : Set Nat.Primes) R := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  rw [IsPiGroup_iff]
  intro q hq
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  have hq_p : q.val ∣ p.val := q.2.dvd_of_dvd_pow (by simpa [hn] using hq)
  exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hq_p)

omit [IsMinCE G] in
public theorem CFSG.section12_isPGroup_of_isPiSubgroup_singleton
    {H : Subgroup G} {q : Nat.Primes}
    (hH : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) H) :
    IsPGroup q.val H := by
  letI : Fact q.val.Prime := ⟨q.2⟩
  rw [IsPGroup.iff_card]
  have hcard_ne_zero : Nat.card H ≠ 0 := Nat.card_pos.ne'
  refine ⟨(Nat.card H).primeFactorsList.length, ?_⟩
  rw [← List.prod_replicate, ← List.eq_replicate_of_mem ?_,
    Nat.prod_primeFactorsList hcard_ne_zero]
  intro p hp
  obtain ⟨hp_prime, hp_dvd⟩ := (Nat.mem_primeFactorsList hcard_ne_zero).mp hp
  let p' : Nat.Primes := ⟨p, hp_prime⟩
  have hp_mem : p' ∈ ({q} : Set Nat.Primes) := hH p' hp_dvd
  simpa [p'] using congrArg Subtype.val hp_mem

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_pSubgroup_le_pCore_of_nilpotent_pre
    {R : Type*} [Group R] [Finite R] [Group.IsNilpotent R]
    {p : ℕ} [Fact p.Prime] {B : Subgroup R} (hBp : IsPGroup p B) :
    B ≤ pCore p R := by
  obtain ⟨S, hB_le_S⟩ := IsPGroup.exists_le_sylow (G := R) (p := p) hBp
  have hS_normal : (S : Subgroup R).Normal :=
    Group.IsNilpotent.sylow_normal (p := p) inferInstance S
  exact hB_le_S.trans (le_sSup ⟨hS_normal, S.isPGroup'⟩)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_eq_bot_of_isPiSubgroup_map_of_isPiGroup_pre
    {π : Set Nat.Primes} {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    {K : Subgroup R} (hK : IsPiSubgroup (G := R) πᶜ K)
    (hS : IsPiGroup π S) (f : R →* S) :
    K.map f = ⊥ := by
  by_contra hmap_ne_bot
  have hcard_ne_one : Nat.card (K.map f) ≠ 1 := by
    intro hcard
    exact hmap_ne_bot ((Subgroup.card_eq_one (H := K.map f)).1 hcard)
  obtain ⟨q, hqPrime, hqMap⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let q' : Nat.Primes := ⟨q, hqPrime⟩
  have hq_mem : q' ∈ π := by
    exact (IsPiGroup_iff π S).1 hS q'
      (hqMap.trans (Subgroup.card_subgroup_dvd_card (K.map f)))
  have hq_not_mem : q' ∉ π := by
    simpa using (section12_isPiSubgroup_map hK f) q' hqMap
  exact hq_not_mem hq_mem

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_subgroup_le_of_subgroupOf_quotient_map_eq_bot_pre
    {N L C : Subgroup G} [hN : (N.subgroupOf L).Normal]
    (hCL : C ≤ L)
    (hmap : (C.subgroupOf L).map (QuotientGroup.mk' (N.subgroupOf L)) = ⊥) :
    C ≤ N := by
  intro x hxC
  have hxsub : (⟨x, hCL hxC⟩ : L) ∈ C.subgroupOf L := by
    simpa [Subgroup.mem_subgroupOf] using hxC
  have hxmap :
      QuotientGroup.mk' (N.subgroupOf L) (⟨x, hCL hxC⟩ : L) ∈
        (C.subgroupOf L).map (QuotientGroup.mk' (N.subgroupOf L)) :=
    Subgroup.mem_map_of_mem (QuotientGroup.mk' (N.subgroupOf L)) hxsub
  have hxbot :
      QuotientGroup.mk' (N.subgroupOf L) (⟨x, hCL hxC⟩ : L) = 1 := by
    simpa [hmap] using hxmap
  have hxker : (⟨x, hCL hxC⟩ : L) ∈ (QuotientGroup.mk' (N.subgroupOf L)).ker := by
    simpa [MonoidHom.mem_ker] using hxbot
  have hxNsub : (⟨x, hCL hxC⟩ : L) ∈ N.subgroupOf L := by
    simpa [QuotientGroup.ker_mk'] using hxker
  simpa [Subgroup.mem_subgroupOf] using hxNsub

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_commutator_le_left_of_le_normalizer_pre
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
public theorem CFSG.section12_commutator_le_right_of_normal_subgroupOf_pre
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

public theorem CFSG.section12_commutator_le_msigma_of_sigma_rankTwo_pre
    {M A K : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∈ section10SigmaPrimes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hKle : K ≤ M) :
    ⁅K, A⁆ ≤ section10Msigma M := by
  have hAσ : A ≤ section10Msigma M :=
    section12_rankTwo_le_msigma_of_sigma hM hpσ hA
  have hσM : section10Msigma M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hσsub_norm : ((section10Msigma M).subgroupOf M).Normal := by
    simpa [section12Msigma_subgroupOf_eq] using
      section10MsigmaSubgroup_normal (M := M)
  haveI : ((section10Msigma M).subgroupOf M).Normal := hσsub_norm
  exact section12_commutator_le_right_of_normal_subgroupOf_pre
    (M := M) (N := section10Msigma M) (K := K) (A := A)
    hσM hKle hAσ

public theorem CFSG.section12_isPiSubgroup_pPrime_of_le_msigma_pre
    {M K : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∉ section10SigmaPrimes M)
    (hKle : K ≤ section10Msigma M) :
    IsPiSubgroup (G := G) (section10PPrimeSet p) K := by
  intro q hqK
  have hqσ : q ∈ section10SigmaPrimes M := by
    exact (theorem_10_2_b (M := M) hM).1.p_in_pi_of_p_dvd_card q
      (hqK.trans (Subgroup.card_dvd_of_le hKle))
  show q ∉ ({p} : Set Nat.Primes)
  intro hq_eq
  have hqp : q = p := by simpa using hq_eq
  exact hpσ (by simpa [hqp] using hqσ)

public theorem CFSG.section12_isPiSubgroup_pPrime_of_le_malpha_pre
    {M K : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpα : p ∉ section10AlphaPrimes M)
    (hKle : K ≤ section10Malpha M) :
    IsPiSubgroup (G := G) (section10PPrimeSet p) K := by
  intro q hqK
  have hqα : q ∈ section10AlphaPrimes M := by
    exact (theorem_10_2_a (M := M) hM).1.p_in_pi_of_p_dvd_card q
      (hqK.trans (Subgroup.card_dvd_of_le hKle))
  show q ∉ ({p} : Set Nat.Primes)
  intro hq_eq
  have hqp : q = p := by simpa using hq_eq
  exact hpα (by simpa [hqp] using hqα)

public theorem CFSG.section12_commutator_le_msigma_of_not_sigma_rankTwo_pre
    {M A A₀ K : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∉ section10SigmaPrimes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (hNA₀ : Subgroup.normalizer (A₀ : Set G) ≤ M)
    (hKle : K ≤ M)
    (hKp' : IsPiSubgroup (G := G) (section10PPrimeSet p) K)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    ⁅K, A⁆ ≤ section10Msigma M := by
  classical
  obtain ⟨P, h11⟩ :=
    section12_exists_section11Data_of_not_sigma_pre (M := M) (A := A) (A₀ := A₀)
      (p := p) hM hpσ hA hA₀ hNA₀
  let N : Subgroup G := section10Msigma M
  let L : Subgroup G := A ⊔ N
  have hnormIn : section10NormalIn L M := by
    simpa [L, N, sup_comm] using theorem_11_7 (M := M) (A0 := A₀) (A := A) (p := p)
      (P := P) h11
  rcases hnormIn with ⟨hLleM, hLnorm⟩
  haveI : (L.subgroupOf M).Normal := hLnorm
  have hAleL : A ≤ L := by
    intro x hx
    exact Subgroup.mem_sup_left hx
  have hC_le_K : ⁅K, A⁆ ≤ K :=
    section12_commutator_le_left_of_le_normalizer_pre hAK
  have hC_le_L : ⁅K, A⁆ ≤ L :=
    section12_commutator_le_right_of_normal_subgroupOf_pre
      (M := M) (N := L) (K := K) (A := A) hLleM hKle hAleL
  let C : Subgroup G := ⁅K, A⁆
  have hC_p' : IsPiSubgroup (G := G) (section10PPrimeSet p) C :=
    IsPiSubgroup.of_le hC_le_K hKp'
  have hCsub_p' : IsPiSubgroup (G := L) (section10PPrimeSet p) (C.subgroupOf L) :=
    section12_isPiSubgroup_subgroupOf_pre hC_p' hC_le_L
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := by
    exact (section12_rankTwo_le hA).trans (by simpa [N] using section12_le_normalizer_msigma)
  have hAelem : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G :=
    section12_rankTwo_elementary hA
  have hAp : IsPGroup p.val A := by
    rcases hAelem with ⟨_hcard, hElem⟩
    haveI : IsElementaryAbelian p.val A := hElem
    exact IsElementaryAbelian.isPGroup p.val A
  haveI : (N.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hAN
  haveI : (N.subgroupOf L).Normal := by
    simpa [L] using
      Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := A) (N := N) hAN
  have hAquot : IsPGroup p.val (A ⧸ N.subgroupOf A) :=
    hAp.to_quotient (N.subgroupOf A)
  let e : A ⧸ N.subgroupOf A ≃* L ⧸ N.subgroupOf L := by
    simpa [L] using QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have hLquot : IsPGroup p.val (L ⧸ N.subgroupOf L) :=
    IsPGroup.of_equiv hAquot e
  have hmap_bot :
      (C.subgroupOf L).map (QuotientGroup.mk' (N.subgroupOf L)) = ⊥ :=
    section12_eq_bot_of_isPiSubgroup_map_of_isPiGroup_pre
      (π := ({p} : Set Nat.Primes)) (K := C.subgroupOf L)
      (by simpa [section10PPrimeSet] using hCsub_p')
      (section12_isPiGroup_singleton_of_isPGroup_pre hLquot)
      (QuotientGroup.mk' (N.subgroupOf L))
  exact section12_subgroup_le_of_subgroupOf_quotient_map_eq_bot_pre
    (N := N) (L := L) (C := C) hC_le_L hmap_bot

public theorem CFSG.section12_commutator_le_malpha_of_sigma_rankTwo_pre
    {M A K : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∈ section10SigmaPrimes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hKle : K ≤ M)
    (hKp' : IsPiSubgroup (G := G) (section10PPrimeSet p) K)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    ⁅K, A⁆ ≤ section10Malpha M := by
  classical
  letI : Fact p.val.Prime := ⟨p.2⟩
  let α : Subgroup M := section10MalphaSubgroup M
  let D : Subgroup M := derivedSubgroup M
  rcases (theorem_10_2_d (M := M) hM).2 with ⟨hαD, hαDnorm, hDquot_nil⟩
  haveI : (α.subgroupOf D).Normal := by
    simpa [α, D] using hαDnorm
  haveI : α.Normal := by
    dsimp [α]
    infer_instance
  let qM : M →* M ⧸ α := QuotientGroup.mk' α
  let Dbar : Subgroup (M ⧸ α) := D.map qM
  have hDbar_norm : Dbar.Normal := by
    dsimp [Dbar]
    exact Subgroup.Normal.map (H := D) inferInstance qM (QuotientGroup.mk'_surjective α)
  haveI : Dbar.Normal := hDbar_norm
  have hDbar_nil : Group.IsNilpotent Dbar := by
    let e : D ⧸ α.subgroupOf D ≃* Dbar := quotientSubgroupRangeEquiv D α
    exact Group.nilpotent_of_mulEquiv (G := D ⧸ α.subgroupOf D) (G' := Dbar) e
  let PbarSub : Subgroup Dbar := pCore p.val Dbar
  have hPbarSub_char : PbarSub.Characteristic := by
    dsimp [PbarSub]
    exact pCore_characteristic (G := Dbar) (p := p.val)
  haveI : PbarSub.Characteristic := hPbarSub_char
  let Pbar : Subgroup (M ⧸ α) := PbarSub.map Dbar.subtype
  have hPbar_norm : Pbar.Normal := by
    dsimp [Pbar]
    infer_instance
  let Nsub : Subgroup M := Pbar.comap qM
  have hNsub_norm : Nsub.Normal := by
    dsimp [Nsub]
    exact hPbar_norm.comap qM
  let N : Subgroup G := Nsub.map M.subtype
  have hNle : N ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hNsub_eq : N.subgroupOf M = Nsub := by
    simpa [N] using subgroupOf_map_subtype_eq (K := M) Nsub
  have hNnorm : (N.subgroupOf M).Normal := by
    rw [hNsub_eq]
    exact hNsub_norm
  have hAM : A ≤ M := section12_rankTwo_le hA
  have hAσ : A ≤ section10Msigma M :=
    section12_rankTwo_le_msigma_of_sigma hM hpσ hA
  have hA_sub_sigma : A.subgroupOf M ≤ section10MsigmaSubgroup M := by
    intro x hx
    have hxA : ((x : M) : G) ∈ A := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxσ : ((x : M) : G) ∈ section10Msigma M := hAσ hxA
    have hxσsub : x ∈ (section10Msigma M).subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hxσ
    simpa [section12Msigma_subgroupOf_eq] using hxσsub
  have hA_sub_D : A.subgroupOf M ≤ D :=
    hA_sub_sigma.trans (by simpa [D] using (theorem_10_2_c (M := M) hM).2)
  let AbarM : Subgroup (M ⧸ α) := (A.subgroupOf M).map qM
  have hAbar_p : IsPGroup p.val AbarM :=
    IsPGroup.map (section12_rankTwo_subgroupOf_isPGroup hA) qM
  have hAbar_le_Dbar : AbarM ≤ Dbar := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hxA, rfl⟩
    exact Subgroup.mem_map.mpr ⟨x, hA_sub_D hxA, rfl⟩
  have hAbarD_p : IsPGroup p.val (AbarM.subgroupOf Dbar) := by
    let e : AbarM.subgroupOf Dbar ≃* AbarM :=
      Subgroup.subgroupOfEquivOfLe hAbar_le_Dbar
    exact hAbar_p.of_equiv e.symm
  have hAbarD_le_pcore : AbarM.subgroupOf Dbar ≤ PbarSub := by
    haveI : Group.IsNilpotent Dbar := hDbar_nil
    simpa [PbarSub] using
      section12_pSubgroup_le_pCore_of_nilpotent_pre (R := Dbar) (p := p.val)
        (B := AbarM.subgroupOf Dbar) hAbarD_p
  have hA_le_N : A ≤ N := by
    intro x hxA
    refine Subgroup.mem_map.mpr ?_
    refine ⟨⟨x, hAM hxA⟩, ?_, rfl⟩
    change qM ⟨x, hAM hxA⟩ ∈ Pbar
    have hxAbar : qM ⟨x, hAM hxA⟩ ∈ AbarM := by
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hAM hxA⟩, by simpa [Subgroup.mem_subgroupOf] using hxA, rfl⟩
    have hxDbar : qM ⟨x, hAM hxA⟩ ∈ Dbar :=
      hAbar_le_Dbar hxAbar
    have hxsub :
        (⟨qM ⟨x, hAM hxA⟩, hxDbar⟩ : Dbar) ∈ AbarM.subgroupOf Dbar := by
      simpa [Subgroup.mem_subgroupOf] using hxAbar
    have hxpcore : (⟨qM ⟨x, hAM hxA⟩, hxDbar⟩ : Dbar) ∈ PbarSub :=
      hAbarD_le_pcore hxsub
    exact Subgroup.mem_map.mpr ⟨⟨qM ⟨x, hAM hxA⟩, hxDbar⟩, hxpcore, rfl⟩
  let C : Subgroup G := ⁅K, A⁆
  have hC_le_K : C ≤ K := by
    simpa [C] using section12_commutator_le_left_of_le_normalizer_pre hAK
  have hC_le_M : C ≤ M := hC_le_K.trans hKle
  have hC_le_N : C ≤ N := by
    haveI : (N.subgroupOf M).Normal := hNnorm
    simpa [C] using
      section12_commutator_le_right_of_normal_subgroupOf_pre
        (M := M) (N := N) (K := K) (A := A) hNle hKle hA_le_N
  let Cbar : Subgroup (M ⧸ α) := (C.subgroupOf M).map qM
  have hC_pi' : IsPiSubgroup (G := G) (section10PPrimeSet p) C :=
    IsPiSubgroup.of_le hC_le_K hKp'
  have hCsub_pi' : IsPiSubgroup (G := M) (section10PPrimeSet p) (C.subgroupOf M) :=
    section12_isPiSubgroup_subgroupOf_pre hC_pi' hC_le_M
  have hCbar_pi' : IsPiSubgroup (G := M ⧸ α) (section10PPrimeSet p) Cbar := by
    simpa [Cbar] using section12_isPiSubgroup_map hCsub_pi' qM
  have hPbar_p : IsPGroup p.val Pbar := by
    dsimp [Pbar, PbarSub]
    exact IsPGroup.map (pCore_isPGroup (G := Dbar) (p := p.val)) Dbar.subtype
  have hPbar_pi : IsPiSubgroup (G := M ⧸ α) ({p} : Set Nat.Primes) Pbar :=
    section8_isPiSubgroup_singleton_of_isPGroup hPbar_p
  have hCbar_le_Pbar : Cbar ≤ Pbar := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hxC, rfl⟩
    have hxCG : ((x : M) : G) ∈ C := by
      simpa [Subgroup.mem_subgroupOf] using hxC
    have hxN : ((x : M) : G) ∈ N := hC_le_N hxCG
    rcases Subgroup.mem_map.mp hxN with ⟨z, hzN, hzx⟩
    have hz_eq : z = x := M.subtype_injective hzx
    have hxNsub : x ∈ Nsub := by
      simpa [hz_eq] using hzN
    exact hxNsub
  have hCbar_pi : IsPiSubgroup (G := M ⧸ α) ({p} : Set Nat.Primes) Cbar :=
    IsPiSubgroup.of_le hCbar_le_Pbar hPbar_pi
  have hCbar_bot : Cbar = ⊥ := by
    exact section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
      (π := ({p} : Set Nat.Primes)) (H := Cbar) (Y := Cbar) (C := Cbar)
      le_rfl le_rfl (by simpa [section10PPrimeSet] using hCbar_pi') hCbar_pi
  intro x hxC
  have hxM : x ∈ M := hC_le_M hxC
  let xM : M := ⟨x, hxM⟩
  have hxCsub : xM ∈ C.subgroupOf M := by
    simpa [xM, Subgroup.mem_subgroupOf] using hxC
  have hxmap : qM xM ∈ Cbar := Subgroup.mem_map.mpr ⟨xM, hxCsub, rfl⟩
  have hxone : qM xM = 1 := by
    simpa [hCbar_bot] using hxmap
  have hxker : xM ∈ qM.ker := by
    simpa [MonoidHom.mem_ker] using hxone
  have hxα : xM ∈ α := by
    simpa [qM, QuotientGroup.ker_mk'] using hxker
  change x ∈ (section10MalphaSubgroup M).map M.subtype
  exact Subgroup.mem_map.mpr ⟨xM, by simpa [α] using hxα, rfl⟩

public theorem CFSG.section12_not_conjugate_of_sigma_rankTwo_pre
    {M Mstar A A₀ : Subgroup G} {p : Nat.Primes}
    (_hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G) (hMstar_ne : Mstar ≠ M)
    (hpσstar : p ∈ section10SigmaPrimes Mstar)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p (M ⊓ Mstar))
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (hNA₀ : Subgroup.normalizer (A₀ : Set G) ≤ Mstar) :
    section12NotConjugate M Mstar := by
  classical
  intro g hconj
  have hAM : A ≤ M := (section12_rankTwo_le hA).trans inf_le_left
  have hAstar : A ∈ section12RankTwoElementaryAbelianIn p Mstar :=
    section12_rankTwo_of_inf_right_pre hA
  have hAMstar : A ≤ Mstar := section12_rankTwo_le hAstar
  have hAelem : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G :=
    section12_rankTwo_elementary hAstar
  have hAp : IsPGroup p.val A := by
    rcases hAelem with ⟨_hcard, hElem⟩
    haveI : IsElementaryAbelian p.val A := hElem
    exact IsElementaryAbelian.isPGroup p.val A
  have hAne : A ≠ ⊥ := by
    rcases hAelem with ⟨hcard, _hElem⟩
    intro hbot
    have hcard_bot : Nat.card A = 1 :=
      (Subgroup.card_eq_one (H := A)).2 hbot
    have hp2ne : p.val ^ 2 ≠ 1 := by
      have hp1 : 1 ≤ p.val := le_of_lt p.2.one_lt
      have hle : p.val ≤ p.val ^ 2 := le_self_pow hp1 (by decide : (2 : ℕ) ≠ 0)
      exact ne_of_gt (lt_of_lt_of_le p.2.one_lt hle)
    have hp2eq : p.val ^ 2 = 1 := by
      rw [← hcard, hcard_bot]
    exact hp2ne hp2eq
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hA₀) with ⟨hA₀A, _hA₀card⟩
  have hCentA_le_Mstar : Subgroup.centralizer (A : Set G) ≤ Mstar := by
    have hCentA_le_CentA₀ :
        Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (A₀ : Set G) :=
      Subgroup.centralizer_le (show (A₀ : Set G) ⊆ (A : Set G) from hA₀A)
    exact hCentA_le_CentA₀.trans ((centralizer_le_normalizer A₀).trans hNA₀)
  have htrans :
      ConjugationActionTransitiveOn (Subgroup.centralizer (A : Set G))
        (section10ConjugatesContaining Mstar A) :=
    theorem_10_1_b (G := G) hMstar hpσstar hAne hAp hAMstar
  have hMstar_mem : Mstar ∈ section10ConjugatesContaining Mstar A :=
    section12_mem_conjugates_self_pre hAMstar
  have hM_mem : M ∈ section10ConjugatesContaining Mstar A :=
    ⟨g⁻¹, section12_eq_conjBy_inv_of_conjBy_eq_pre hconj, hAM⟩
  have hM_eq_Mstar : M = Mstar :=
    section12_eq_of_conjugation_transitive_and_centralizer_le_pre
      htrans hMstar_mem hM_mem hCentA_le_Mstar
  exact hMstar_ne hM_eq_Mstar.symm

/-- Lemma 12.3(a). -/
public theorem CFSG.lemma_12_3_a
    {M Mstar A A₀ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G) (hMstar_ne : Mstar ≠ M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p (M ⊓ Mstar))
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (hNA₀ : Subgroup.normalizer (A₀ : Set G) ≤ Mstar)
    (hpσ : p ∉ section10SigmaPrimes M) :
    A ≤ Subgroup.centralizer (section10Msigma M ⊓ Mstar : Set G) := by
  classical
  let K : Subgroup G := section10Msigma M ⊓ Mstar
  let C : Subgroup G := ⁅K, A⁆
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_inf_left_pre hA
  have hA_Mstar : A ∈ section12RankTwoElementaryAbelianIn p Mstar :=
    section12_rankTwo_of_inf_right_pre hA
  have hAM : A ≤ M := section12_rankTwo_le hA_M
  have hKleMstar : K ≤ Mstar := inf_le_right
  have hKleMsigma : K ≤ section10Msigma M := inf_le_left
  have hKp' : IsPiSubgroup (G := G) (section10PPrimeSet p) K :=
    section12_isPiSubgroup_pPrime_of_le_msigma_pre hM hpσ hKleMsigma
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
    simpa [K] using section12_rankTwo_le_normalizer_msigma_inf_pre (M := M) (Mstar := Mstar) hA
  have hC_le_K : C ≤ K := by
    simpa [C] using section12_commutator_le_left_of_le_normalizer_pre hAK
  have hC_le_Msigma : C ≤ section10Msigma M := hC_le_K.trans hKleMsigma
  have hCbot : C = ⊥ := by
    by_cases hpσstar : p ∈ section10SigmaPrimes Mstar
    · have hC_le_alpha_star : C ≤ section10Malpha Mstar := by
        simpa [C] using
          section12_commutator_le_malpha_of_sigma_rankTwo_pre
            (M := Mstar) (A := A) (K := K) (p := p)
            hMstar hpσstar hA_Mstar hKleMstar hKp' hAK
      have hnotconj : section12NotConjugate M Mstar :=
        section12_not_conjugate_of_sigma_rankTwo_pre
          (M := M) (Mstar := Mstar) (A := A) (A₀ := A₀) (p := p)
          hM hMstar hMstar_ne hpσstar hA hA₀ hNA₀
      have hdis :
          Disjoint (section10Malpha Mstar) (section10Msigma M) :=
        (lemma_10_12_a (G := G) (M := Mstar) (H := M)
          hMstar hM hnotconj).1
      have hC_le_inf : C ≤ section10Malpha Mstar ⊓ section10Msigma M := by
        intro x hx
        exact ⟨hC_le_alpha_star hx, hC_le_Msigma hx⟩
      exact le_bot_iff.mp (by
        rw [← hdis.eq_bot]
        exact hC_le_inf)
    · have hC_le_sigma_star : C ≤ section10Msigma Mstar := by
        simpa [C] using
          section12_commutator_le_msigma_of_not_sigma_rankTwo_pre
            (M := Mstar) (A := A) (A₀ := A₀) (K := K) (p := p)
            hMstar hpσstar hA_Mstar hA₀ hNA₀ hKleMstar hKp' hAK
      by_contra hCne
      obtain ⟨P, h11⟩ :=
        section12_exists_section11Data_of_not_sigma_pre
          (M := Mstar) (A := A) (A₀ := A₀) (p := p)
          hMstar hpσstar hA_Mstar hA₀ hNA₀
      have hMcont : M ∈ section9MaximalSubgroupsContaining A := ⟨hM, hAM⟩
      have hinter : section10Msigma Mstar ⊓ section10Msigma M ≠ ⊥ := by
        intro hinter_bot
        have hC_le_inf : C ≤ section10Msigma Mstar ⊓ section10Msigma M := by
          intro x hx
          exact ⟨hC_le_sigma_star hx, hC_le_Msigma hx⟩
        have hC_bot' : C = ⊥ :=
          le_bot_iff.mp (by
            rw [← hinter_bot]
            exact hC_le_inf)
        exact hCne hC_bot'
      have hEq : Mstar = M :=
        corollary_11_4 (G := G) (M := Mstar) (A0 := A₀) (A := A)
          (H := M) (p := p) (P := P) h11 hMcont hinter
      exact hMstar_ne hEq
  have hK_le_centA : K ≤ Subgroup.centralizer (A : Set G) := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K) (H₂ := A)).mp
      (by simpa [C] using hCbot)
  exact (Subgroup.le_centralizer_iff (H := K) (K := A)).mp hK_le_centA


end Section12
