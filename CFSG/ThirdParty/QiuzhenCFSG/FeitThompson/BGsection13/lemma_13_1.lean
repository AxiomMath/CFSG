module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Lemma 13 1 from BG Section 13 -/

section Section13

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_le_normalizer_msigma {M : Subgroup G} :
    M ≤ Subgroup.normalizer (section10Msigma M : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases hx with ⟨s, hs, rfl⟩
    exact Subgroup.mem_map_of_mem M.subtype
      (Subgroup.Normal.conj_mem inferInstance s hs ⟨m, hm⟩)
  · intro hx
    rcases hx with ⟨s, hs, hsx⟩
    refine ⟨(⟨m, hm⟩ : M)⁻¹ * s * ⟨m, hm⟩, ?_, ?_⟩
    · simpa using
        Subgroup.Normal.conj_mem inferInstance s hs ((⟨m, hm⟩ : M)⁻¹)
    · calc
        ((((⟨m, hm⟩ : M)⁻¹ * s * ⟨m, hm⟩ : M) : G)) =
            m⁻¹ * ((s : M) : G) * m := by rfl
        _ = m⁻¹ * (m * x * m⁻¹) * m := by
          have hsx' : (s : G) = m * x * m⁻¹ := hsx
          rw [hsx']
        _ = x := by simp [mul_assoc]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_le_normalizer_inf
    {A H K : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer (H ⊓ K : Set G) := by
  intro a ha
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hAH ha, hAK ha⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_subgroupCentralizerIn_commute
    (A S : Subgroup G) :
    S ≤ Subgroup.centralizer (subgroupCentralizerIn A S : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  exact (Subgroup.mem_centralizer_iff.mp hc.2 s hs).symm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_le_normalizer_subgroupCentralizerIn
    {A P S : Subgroup G}
    (hS_norm_A : S ≤ Subgroup.normalizer (A : Set G))
    (hS_cent_P : S ≤ Subgroup.centralizer (P : Set G)) :
    S ≤ Subgroup.normalizer (subgroupCentralizerIn A P : Set G) := by
  have hS_norm_cent :
      S ≤ Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) :=
    hS_cent_P.trans
      (Subgroup.le_normalizer :
        Subgroup.centralizer (P : Set G) ≤
          Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G))
  simpa [subgroupCentralizerIn] using
    section13_le_normalizer_inf
      (G := G) (A := S) (H := A) (K := Subgroup.centralizer (P : Set G))
      hS_norm_A hS_norm_cent

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_commutator_le_left_of_le_normalizer
    {K P : Subgroup G}
    (hPnormK : P ≤ Subgroup.normalizer (K : Set G)) :
    ⁅K, P⁆ ≤ K := by
  let S : Subgroup G := P ⊔ K
  have hKnorm : (K.subgroupOf S).Normal := by
    simpa [S] using
      Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := P) (N := K) hPnormK
  haveI : (K.subgroupOf S).Normal := hKnorm
  intro x hx
  have hxmap : x ∈ (⁅K.subgroupOf S, P.subgroupOf S⁆).map S.subtype := by
    rw [commutator_subgroupOf_map_eq S P K le_sup_left le_sup_right]
    exact hx
  rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, rfl⟩
  exact (Subgroup.commutator_le_left
      (H₁ := K.subgroupOf S) (H₂ := P.subgroupOf S)) hy

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_subgroupCentralizerIn_sup_of_le_centralizer
    {A R Q C : Subgroup G}
    (hC_AR : C ≤ subgroupCentralizerIn A R)
    (hC_cent_Q : C ≤ Subgroup.centralizer (Q : Set G)) :
    C ≤ subgroupCentralizerIn A (R ⊔ Q) := by
  have hC_cent_R : C ≤ Subgroup.centralizer (R : Set G) := by
    intro x hx
    exact (hC_AR hx).2
  have hR_cent_C : R ≤ Subgroup.centralizer (C : Set G) :=
    (Subgroup.le_centralizer_iff (H := C) (K := R)).mp hC_cent_R
  have hQ_cent_C : Q ≤ Subgroup.centralizer (C : Set G) :=
    (Subgroup.le_centralizer_iff (H := C) (K := Q)).mp hC_cent_Q
  have hRQ_cent_C : R ⊔ Q ≤ Subgroup.centralizer (C : Set G) :=
    sup_le hR_cent_C hQ_cent_C
  have hC_cent_RQ : C ≤ Subgroup.centralizer ((R ⊔ Q : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff (H := R ⊔ Q) (K := C)).mp hRQ_cent_C
  intro x hx
  exact ⟨(hC_AR hx).1, hC_cent_RQ hx⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_commutator_le_centralizer_of_equal_centralizers
    {A P R S : Subgroup G}
    (hS_norm_CP : S ≤ Subgroup.normalizer (subgroupCentralizerIn A P : Set G))
    (hCP_eq_CR : subgroupCentralizerIn A P = subgroupCentralizerIn A R) :
    ⁅S, R⁆ ≤ Subgroup.centralizer (subgroupCentralizerIn A R : Set G) := by
  let C : Subgroup G := subgroupCentralizerIn A R
  have hR_cent_C : R ≤ Subgroup.centralizer (C : Set G) := by
    simpa [C] using section13_subgroupCentralizerIn_commute (G := G) A R
  have hRC_bot : ⁅R, C⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := R) (H₂ := C)).2 hR_cent_C
  have hS_norm_C : S ≤ Subgroup.normalizer (C : Set G) := by
    simpa [C, hCP_eq_CR] using hS_norm_CP
  have hCS_le_C : ⁅C, S⁆ ≤ C :=
    section13_commutator_le_left_of_le_normalizer hS_norm_C
  have hC_cent_R : C ≤ Subgroup.centralizer (R : Set G) := by
    intro x hx
    exact (show x ∈ subgroupCentralizerIn A R from hx).2
  have hCS_cent_R : ⁅C, S⁆ ≤ Subgroup.centralizer (R : Set G) :=
    hCS_le_C.trans hC_cent_R
  have hCSR_bot : ⁅⁅C, S⁆, R⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ⁅C, S⁆) (H₂ := R)).2
      hCS_cent_R
  have hRCS_bot : ⁅⁅R, C⁆, S⁆ = ⊥ := by
    simp [hRC_bot]
  have hSRC_bot : ⁅⁅S, R⁆, C⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate
      (H₁ := S) (H₂ := R) (H₃ := C) hRCS_bot hCSR_bot
  exact
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ⁅S, R⁆) (H₂ := C)).1
      hSRC_bot

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_subgroupCentralizerIn_le_sup_of_equal_centralizers
    {A P R S : Subgroup G}
    (hS_norm_CP : S ≤ Subgroup.normalizer (subgroupCentralizerIn A P : Set G))
    (hCP_eq_CR : subgroupCentralizerIn A P = subgroupCentralizerIn A R) :
    subgroupCentralizerIn A R ≤ subgroupCentralizerIn A (R ⊔ ⁅S, R⁆) := by
  have hcomm_cent :
      ⁅S, R⁆ ≤ Subgroup.centralizer (subgroupCentralizerIn A R : Set G) :=
    section13_commutator_le_centralizer_of_equal_centralizers
      (G := G) (A := A) (P := P) (R := R) (S := S) hS_norm_CP hCP_eq_CR
  have hC_cent_comm :
      subgroupCentralizerIn A R ≤ Subgroup.centralizer ((⁅S, R⁆ : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff (H := ⁅S, R⁆) (K := subgroupCentralizerIn A R)).mp
      hcomm_cent
  exact
    section13_subgroupCentralizerIn_sup_of_le_centralizer
      (G := G) (A := A) (R := R) (Q := ⁅S, R⁆)
      (C := subgroupCentralizerIn A R) le_rfl hC_cent_comm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_not_unique_of_le_two_distinct_maximal
    {L M N : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) (hN : N ∈ section9MaximalSubgroups G)
    (hLM : L ≤ M) (hLN : L ≤ N) (hNM : N ≠ M) :
    L ∉ section9UniqueSubgroups G := by
  classical
  intro hL
  rcases hL with ⟨_hLproper, U, hUuniq⟩
  have hMcont : M ∈ section9MaximalSubgroupsContaining L := ⟨hM, hLM⟩
  have hNcont : N ∈ section9MaximalSubgroupsContaining L := ⟨hN, hLN⟩
  have hMU : M = U := by
    have hsingle : M ∈ ({U} : Set (Subgroup G)) := by
      simpa [hUuniq] using hMcont
    simpa using hsingle
  have hNU : N = U := by
    have hsingle : N ∈ ({U} : Set (Subgroup G)) := by
      simpa [hUuniq] using hNcont
    simpa using hsingle
  exact hNM (hNU.trans hMU.symm)

omit [IsMinCE G] in
public theorem CFSG.section13_commutator_centralizerIn_eq_bot_of_coprime
    {K P : Subgroup G}
    (hPnormK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card K))
    (hKcomm : IsMulCommutative K) :
    subgroupCentralizerIn ⁅K, P⁆ P = ⊥ := by
  classical
  haveI : Subgroup.Normalizes P K := ⟨hPnormK⟩
  let Cfix : Subgroup K := fixedPointSubgroup (↥P) (↥K)
  let Ccomm : Subgroup K := commutatorAction (A := ↥P) (G := ↥K)
  have hfixed_eq :
      Cfix = (subgroupCentralizerIn K P).subgroupOf K := by
    simpa [Cfix] using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn K P hPnormK
  have hcomm_map : Ccomm.map K.subtype = ⁅K, P⁆ := by
    simpa [Ccomm] using
      commutatorAction_subgroup_conj_map_eq_commutator K P hPnormK
  have hsolvK : IsSolvable K := by
    exact isSolvable_of_comm fun x y => (hKcomm.is_comm).comm x y
  have hcompl : IsCompl Cfix Ccomm := by
    simpa [Cfix, Ccomm] using
      (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := K) (A := P) hsolvK hcop hKcomm)
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases hx with ⟨hxK0, hxCentP⟩
  have hxK : x ∈ K :=
    section13_commutator_le_left_of_le_normalizer hPnormK hxK0
  let xK : K := ⟨x, hxK⟩
  have hxFix : xK ∈ Cfix := by
    rw [hfixed_eq]
    change (x : G) ∈ subgroupCentralizerIn K P
    exact ⟨hxK, hxCentP⟩
  have hxComm : xK ∈ Ccomm := by
    have hxMap : x ∈ Ccomm.map K.subtype := by
      simpa [hcomm_map] using hxK0
    rcases Subgroup.mem_map.mp hxMap with ⟨y, hyC, hyx⟩
    have hy_eq : y = xK := Subtype.ext hyx
    simpa [hy_eq] using hyC
  have hxbot : xK ∈ (⊥ : Subgroup K) := by
    have hinf_bot : Cfix ⊓ Ccomm = ⊥ := hcompl.disjoint.eq_bot
    have hxinf : xK ∈ Cfix ⊓ Ccomm := ⟨hxFix, hxComm⟩
    simpa [hinf_bot] using hxinf
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_coprime_card_of_isPiSubgroup_disjoint_primes
    {π ρ : Set Nat.Primes} {A B : Subgroup G}
    (hA : IsPiSubgroup π A) (hB : IsPiSubgroup ρ B)
    (hπρ : Disjoint π ρ) :
    Nat.Coprime (Nat.card A) (Nat.card B) := by
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqA hqB
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hqπ : q' ∈ π := hA q' hqA
  have hqρ : q' ∈ ρ := hB q' hqB
  exact (Set.disjoint_left.mp hπρ hqπ) hqρ

omit [IsMinCE G] in
public theorem CFSG.section13_pSubgroup_le_normal_hall_of_prime_mem
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

omit [IsMinCE G] in
private theorem CFSG.section13_piCore_mono
    {H : Type*} [Group H] [Finite H] {π ρ : Set Nat.Primes}
    (hπρ : π ⊆ ρ) :
    piCore π H ≤ piCore ρ H := by
  have hπ : IsPiSubgroup (G := H) π (piCore π H) :=
    piCore_isPiSubgroup (G := H) π
  have hρ : IsPiSubgroup (G := H) ρ (piCore π H) := by
    intro p hp
    exact hπρ (hπ p hp)
  exact le_piCore_of_normal_isPiSubgroup (G := H) ρ (piCore π H) hρ

omit [IsMinCE G] in
public theorem CFSG.section13_mbeta_le_malpha (M : Subgroup G) :
    section10Mbeta M ≤ section10Malpha M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact Subgroup.mem_map.mpr
    ⟨y,
      section13_piCore_mono
        (H := M) (π := section10BetaPrimes M) (ρ := section10AlphaPrimes M)
        (by intro p hp; exact hp.1) hy,
      rfl⟩

public theorem CFSG.section13_malpha_le_msigma
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    section10Malpha M ≤ section10Msigma M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact Subgroup.mem_map.mpr
    ⟨y, (theorem_10_2_c (G := G) hM).1 hy, rfl⟩

omit [IsMinCE G] in
private theorem CFSG.section13_centralizes_of_commutator_le_pi_compl
    {π : Set Nat.Primes} {K P L : Subgroup G}
    (hPnormK : P ≤ Subgroup.normalizer (K : Set G))
    (hKπ : IsPiSubgroup (G := G) π K)
    (hLπc : IsPiSubgroup (G := G) πᶜ L)
    (hcommL : ⁅K, P⁆ ≤ L) :
    P ≤ Subgroup.centralizer (K : Set G) := by
  have hcommK : ⁅K, P⁆ ≤ K :=
    section13_commutator_le_left_of_le_normalizer hPnormK
  have hcomm_bot : ⁅K, P⁆ = ⊥ :=
    section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
      (G := G) (π := π) hcommL hcommK hLπc hKπ
  have hK_le_centP : K ≤ Subgroup.centralizer (P : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K) (H₂ := P)).mp hcomm_bot
  exact (Subgroup.le_centralizer_iff (H := K) (K := P)).mp hK_le_centP

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_le_normalizer_malpha {M : Subgroup G} :
    M ≤ Subgroup.normalizer (section10Malpha M : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases hx with ⟨s, hs, rfl⟩
    exact Subgroup.mem_map_of_mem M.subtype
      (Subgroup.Normal.conj_mem inferInstance s hs ⟨m, hm⟩)
  · intro hx
    rcases hx with ⟨s, hs, hsx⟩
    refine ⟨(⟨m, hm⟩ : M)⁻¹ * s * ⟨m, hm⟩, ?_, ?_⟩
    · simpa using
        Subgroup.Normal.conj_mem inferInstance s hs ((⟨m, hm⟩ : M)⁻¹)
    · calc
        ((((⟨m, hm⟩ : M)⁻¹ * s * ⟨m, hm⟩ : M) : G)) =
            m⁻¹ * ((s : M) : G) * m := by rfl
        _ = m⁻¹ * (m * x * m⁻¹) * m := by
          have hsx' : (s : G) = m * x * m⁻¹ := hsx
          rw [hsx']
        _ = x := by simp [mul_assoc]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_map_subtype_le_normalizer_of_normal
    (K : Subgroup G) (H : Subgroup K) [H.Normal] :
    K ≤ Subgroup.normalizer (H.map K.subtype : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases hx with ⟨h, hh, rfl⟩
    exact Subgroup.mem_map_of_mem K.subtype
      (Subgroup.Normal.conj_mem inferInstance h hh ⟨k, hk⟩)
  · intro hx
    rcases hx with ⟨h, hh, hhx⟩
    refine ⟨(⟨k, hk⟩ : K)⁻¹ * h * ⟨k, hk⟩, ?_, ?_⟩
    · simpa using
        Subgroup.Normal.conj_mem inferInstance h hh ((⟨k, hk⟩ : K)⁻¹)
    · calc
        (((⟨k, hk⟩ : K)⁻¹ * h * ⟨k, hk⟩ : K) : G) =
            k⁻¹ * ((h : K) : G) * k := by rfl
        _ = k⁻¹ * (k * x * k⁻¹) * k := by
          have hhx' : (h : G) = k * x * k⁻¹ := hhx
          rw [hhx']
        _ = x := by simp [mul_assoc]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_ambient_sylow_le_base {p : Nat.Primes}
    (M : Subgroup G) (S : Sylow p.val M) :
    section10AmbientSylowSubgroup M S ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨s, _hs, rfl⟩
  exact s.property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_conjBy_eq_of_mem_normalizer
    {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    H.conjBy g = H := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).1 hy
  · intro hx
    refine Subgroup.mem_map.mpr ?_
    have hgInv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).inv_mem hg
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp hgInv x).1 hx
    · simp [MulAut.conj_apply, mul_assoc]

omit [IsMinCE G] in
public theorem CFSG.section13_normalizer_inf_sylow_le_right_of_sigma
    {M Mstar : Subgroup G} {q : Nat.Primes}
    {S : Sylow q.val (M ⊓ Mstar : Subgroup G)}
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hqσstar : q ∈ section10SigmaPrimes Mstar)
    (hSylowStar :
      section12SylowSubgroupIn q (section10AmbientSylowSubgroup (M ⊓ Mstar) S)
        Mstar) :
    Subgroup.normalizer
        ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) ≤
      Mstar := by
  classical
  rcases hSylowStar with ⟨Pstar, hPstar⟩
  intro g hg
  refine theorem_10_1_d (G := G) (M := Mstar) (p := q) hMstar hqσstar Pstar ?_
  rw [hPstar, section13_conjBy_eq_of_mem_normalizer hg, ← hPstar]
  exact section13_ambient_sylow_le_base (G := G) Mstar Pstar

omit [IsMinCE G] in
public theorem CFSG.section13_global_sylow_of_inf_sylow_normalizer_le
    {M Mstar : Subgroup G} {q : Nat.Primes}
    {S : Sylow q.val (M ⊓ Mstar : Subgroup G)}
    (hnormM :
      Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) ≤
        M)
    (hnormMstar :
      Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) ≤
        Mstar) :
    ∃ Sg : Sylow q.val G,
      (Sg : Subgroup G) = section10AmbientSylowSubgroup (M ⊓ Mstar) S := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hnormInf :
      Subgroup.normalizer
          (section8SubgroupInAmbient (S : Subgroup (M ⊓ Mstar : Subgroup G)) : Set G) ≤
        M ⊓ Mstar := by
    intro g hg
    have hg' :
        g ∈ Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) := by
      simpa [section10AmbientSylowSubgroup, section8SubgroupInAmbient] using hg
    exact ⟨hnormM hg', hnormMstar hg'⟩
  rcases section8SubgroupInAmbient_sylow_of_normalizer_le
      (G := G) (p := q.val) (M := M ⊓ Mstar) S hnormInf with ⟨Sg, hSg⟩
  refine ⟨Sg, ?_⟩
  simpa [section10AmbientSylowSubgroup, section8SubgroupInAmbient] using hSg

omit [IsMinCE G] in
public theorem CFSG.section13_Mbeta_eq_Malpha_of_alphaPrimes_eq_betaPrimes
    {M : Subgroup G} (hαβ : section10AlphaPrimes M = section10BetaPrimes M) :
    section10Mbeta M = section10Malpha M := by
  simp [section10Mbeta, section10Malpha, section10MbetaSubgroup,
    section10MalphaSubgroup, hαβ]

omit [IsMinCE G] in
public theorem CFSG.section13_Mbeta_ne_bot_of_inf_sup_mbeta_eq
    {M Mstar : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hMstar_ne : Mstar ≠ M)
    (hjoin : M ⊓ Mstar ⊔ section10Mbeta Mstar = Mstar) :
    section10Mbeta Mstar ≠ ⊥ := by
  intro hβbot
  have hMstar_le_M : Mstar ≤ M := by
    intro x hx
    have hxjoin : x ∈ M ⊓ Mstar ⊔ section10Mbeta Mstar := by
      rw [hjoin]
      exact hx
    have hxinf : x ∈ M ⊓ Mstar := by
      simpa [hβbot] using hxjoin
    exact hxinf.1
  have hM_eq_Mstar : M = Mstar := (hMstar.le_iff_eq hM.1).mp hMstar_le_M
  exact hMstar_ne hM_eq_Mstar.symm

omit [IsMinCE G] in
public theorem CFSG.section13_notConjugate_symm
    {H K : Subgroup G} (hnot : section12NotConjugate H K) :
    section12NotConjugate K H := by
  intro g hconj
  have hback : H.conjBy g⁻¹ = K := by
    calc
      H.conjBy g⁻¹ = (K.conjBy g).conjBy g⁻¹ := by rw [hconj]
      _ = K.conjBy (g⁻¹ * g) := section8_conjBy_conjBy K g g⁻¹
      _ = K := by simpa using section8_conjBy_one (G := G) K
  exact hnot g⁻¹ hback

omit [IsMinCE G] in
public theorem CFSG.section13_isPiSubgroup_compl_of_isPGroup_not_mem
    {π : Set Nat.Primes} {p : Nat.Primes} {P : Subgroup G}
    (hpπ : p ∉ π) (hPp : IsPGroup p.val P) :
    IsPiSubgroup (G := G) πᶜ P := by
  intro q hqP
  have hq_singleton : q ∈ ({p} : Set Nat.Primes) :=
    section8_isPiSubgroup_singleton_of_isPGroup hPp q hqP
  have hqp : q = p := by simpa using hq_singleton
  rw [Set.mem_compl_iff]
  intro hqπ
  exact hpπ (by simpa [hqp] using hqπ)

private theorem CFSG.section13_malpha_isPiSubgroup_sigma_compl_of_notconj
    {M Mstar : Subgroup G}
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M) :
    IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ (section10Malpha Mstar) := by
  intro q hqα
  have hαπ : IsPiSubgroup (G := G) (section10AlphaPrimes Mstar)
      (section10Malpha Mstar) := by
    intro r hr
    exact ((theorem_10_2_a (G := G) hMstar).1).p_in_pi_of_p_dvd_card r hr
  have hdis : Disjoint (section10AlphaPrimes Mstar) (section10SigmaPrimes M) :=
    (lemma_10_12_a (G := G) (M := Mstar) (H := M) hMstar hM
      (section13_notConjugate_symm hnotconj)).2
  rw [Set.mem_compl_iff]
  intro hqσ
  rw [Set.disjoint_left] at hdis
  exact hdis (hαπ q hqα) hqσ

omit [IsMinCE G] in
private theorem CFSG.section13_ambient_sylow_isPiSubgroup_sigma_compl_of_not_sigma
    {M Mstar : Subgroup G} {p : Nat.Primes}
    (hpσ : p ∉ section10SigmaPrimes M) (S : Sylow p.val Mstar) :
    IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ
      (section10AmbientSylowSubgroup Mstar S) := by
  have hSp : IsPGroup p.val (section10AmbientSylowSubgroup Mstar S) := by
    change IsPGroup p.val ((S : Subgroup Mstar).map Mstar.subtype)
    exact IsPGroup.map (p := p.val) (H := (S : Subgroup Mstar))
      S.isPGroup' Mstar.subtype
  exact section13_isPiSubgroup_compl_of_isPGroup_not_mem hpσ hSp

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_isPiSubgroup_sup_of_normal_right
    {π : Set Nat.Primes} {H K : Subgroup G}
    (hH : IsPiSubgroup (G := G) π H) (hK : IsPiSubgroup (G := G) π K)
    [K.Normal] :
    IsPiSubgroup (G := G) π (H ⊔ K) := by
  intro p hpSup
  have hmul : (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) := by
    simpa using (Subgroup.mul_normal H K)
  have hcard_sup_set :
      Nat.card (↑(H ⊔ K) : Set G) =
        Nat.card ((H : Set G) * (K : Set G) : Set G) :=
    Nat.card_congr (Set.equivOfEq hmul)
  have hcard_sup :
      Nat.card (↥(H ⊔ K)) = Nat.card ((H : Set G) * (K : Set G) : Set G) := by
    simpa using hcard_sup_set
  have hcard_mul :
      Nat.card ((H : Set G) * (K : Set G) : Set G) =
        Nat.card K * Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) := by
    simpa using
      (Subgroup.card_mul_eq_card_subgroup_mul_card_quotient
        (s := K) (t := (H : Set G)))
  have hset_image :
      ((H : Set G).image (↑) : Set (G ⧸ K)) =
        (H.map (QuotientGroup.mk' K) : Set (G ⧸ K)) := by
    simp [Subgroup.coe_map]
  have hcard_image_set :
      Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) =
        Nat.card (H.map (QuotientGroup.mk' K) : Set (G ⧸ K)) :=
    Nat.card_congr (Set.equivOfEq hset_image)
  have hcard_image_subgroup :
      Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) =
        Nat.card (H.map (QuotientGroup.mk' K)) := by
    exact hcard_image_set
  have hp_mul :
      p.val ∣ Nat.card K * Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) := by
    rw [← hcard_mul, ← hcard_sup]
    exact hpSup
  rcases p.property.dvd_mul.mp hp_mul with hpK | hpImg
  · exact hK p hpK
  · have hpMap : p.val ∣ Nat.card (H.map (QuotientGroup.mk' K)) := by
      rwa [hcard_image_subgroup] at hpImg
    exact hH p (hpMap.trans
      (Subgroup.card_map_dvd (H := H) (QuotientGroup.mk' K)))

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_isPiSubgroup_sup_of_le_normalizer
    {π : Set Nat.Primes} {H K : Subgroup G}
    (hHπ : IsPiSubgroup (G := G) π H) (hKπ : IsPiSubgroup (G := G) π K)
    (hHnormK : H ≤ Subgroup.normalizer (K : Set G)) :
    IsPiSubgroup (G := G) π (H ⊔ K) := by
  classical
  let S : Subgroup G := H ⊔ K
  let Hs : Subgroup S := H.subgroupOf S
  let Ks : Subgroup S := K.subgroupOf S
  have hHsπ : IsPiSubgroup (G := S) π Hs := by
    intro q hq
    have hcard : Nat.card Hs = Nat.card H := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := H) (K := S)
          (by simp [S])).toEquiv
    exact hHπ q (by simpa [hcard] using hq)
  have hKsπ : IsPiSubgroup (G := S) π Ks := by
    intro q hq
    have hcard : Nat.card Ks = Nat.card K := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := K) (K := S)
          (by simp [S])).toEquiv
    exact hKπ q (by simpa [hcard] using hq)
  haveI : Ks.Normal := by
    simpa [S, Ks] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := H) (N := K) hHnormK)
  have hHsKs_top : Hs ⊔ Ks = ⊤ := by
    calc
      Hs ⊔ Ks = S.subgroupOf S := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := H) (A' := K) (B := S)
          (by simp [S])
          (by simp [S])
      _ = ⊤ := by simp
  have htopπ : IsPiSubgroup (G := S) π (⊤ : Subgroup S) := by
    rw [← hHsKs_top]
    exact section13_isPiSubgroup_sup_of_normal_right
      (G := S) (π := π) (H := Hs) (K := Ks) hHsπ hKsπ
  intro q hq
  exact htopπ q (by simpa using hq)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_commutator_le_right_of_le_normalizer
    {K P L : Subgroup G}
    (hKnormL : K ≤ Subgroup.normalizer (L : Set G)) (hPL : P ≤ L) :
    ⁅K, P⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro k hk p hp
  have hk_norm : k ∈ Subgroup.normalizer (L : Set G) := hKnormL hk
  have hconj : k * p * k⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hk_norm p).1 (hPL hp)
  simpa [commutatorElement_def, mul_assoc] using L.mul_mem hconj (L.inv_mem (hPL hp))

public theorem CFSG.section13_sigmaPrimes_mem_of_alphaPrimes_mem
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpα : p ∈ section10AlphaPrimes M) :
    p ∈ section10SigmaPrimes M := by
  classical
  have hpα_mem : p ∈ section10AlphaPrimes M := hpα
  rcases hpα with ⟨hpM, _hprank⟩
  let A : Subgroup M := section10MalphaSubgroup M
  let S : Subgroup M := section10MsigmaSubgroup M
  have hHallA : IsHallSubgroup (section10AlphaPrimes M) A :=
    (theorem_10_2_a (M := M) hM).2
  have hHallS : IsHallSubgroup (section10SigmaPrimes M) S :=
    (theorem_10_2_b (M := M) hM).2
  have hAS : A ≤ S := (theorem_10_2_c (M := M) hM).1
  have hp_not_idx_A : ¬ p.val ∣ A.index := by
    intro hpidx
    exact (hHallA.p_in_pi_of_p_dvd_index p hpidx) hpα_mem
  have hmulA : A.index * Nat.card A = Nat.card M :=
    Subgroup.index_mul_card (H := A)
  have hp_mul : p.val ∣ A.index * Nat.card A := by
    have hpM' : p.val ∣ Nat.card M := by
      simpa [subgroupPrimeSet] using hpM
    rw [hmulA]
    exact hpM'
  rcases p.2.dvd_mul.mp hp_mul with hpidx | hpA
  · exact False.elim (hp_not_idx_A hpidx)
  · have hA_card_dvd_S : Nat.card A ∣ Nat.card S := by
      have hsub_dvd : Nat.card (A.subgroupOf S) ∣ Nat.card S :=
        Subgroup.card_subgroup_dvd_card (A.subgroupOf S)
      have hcard : Nat.card (A.subgroupOf S) = Nat.card A :=
        natCard_subgroupOf_eq A S hAS
      rwa [hcard] at hsub_dvd
    exact hHallS.p_in_pi_of_p_dvd_card p (hpA.trans hA_card_dvd_S)

omit [IsMinCE G] in
private theorem CFSG.section13_one_le_generatorRank_of_nontrivial
    {R : Type*} [Group R] [Finite R] [Nontrivial R] :
    1 ≤ generatorRank R := by
  classical
  rw [generatorRank_eq_group_rank]
  by_contra hlt
  have hrank0 : Group.rank R = 0 := by omega
  obtain ⟨S, hScard, hSgen⟩ := Group.rank_spec R
  have hSempty : S = ∅ := Finset.card_eq_zero.mp (by omega)
  have hclosureS_bot : Subgroup.closure (S : Set R) = ⊥ := by
    simp [hSempty]
  have hbot_top : (⊥ : Subgroup R) = ⊤ := by
    rw [← hclosureS_bot, hSgen]
  have hsub : Subsingleton R := by
    refine ⟨fun x y => ?_⟩
    have hx : x = 1 := by
      have hxbot : x ∈ (⊥ : Subgroup R) := by
        rw [hbot_top]
        exact trivial
      simpa using hxbot
    have hy : y = 1 := by
      have hybot : y ∈ (⊥ : Subgroup R) := by
        rw [hbot_top]
        exact trivial
      simpa using hybot
    rw [hx, hy]
  exact not_subsingleton R hsub

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_generatorRank_le_primeRank_of_subgroup
    {R : Type*} [Group R] [Finite R] {q : ℕ} {A : Subgroup R}
    (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A) :
    generatorRank A ≤ primeRank q R := by
  rw [primeRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
    exact hnB.trans <|
      (section8_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
  · exact ⟨A, hAp, hAcomm, le_rfl⟩

omit [IsMinCE G] in
private theorem CFSG.section13_primeRank_pos_of_mem_subgroupPrimeSet
    {R : Type*} [Group R] [Finite R] {p : Nat.Primes}
    (hpR : p.val ∣ Nat.card R) :
    1 ≤ primeRank p.val R := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  let P : Sylow p.val R := Classical.choice (Sylow.nonempty (p := p.val) (G := R))
  have hP_ne_bot : (P : Subgroup R) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := R) P hpR
  haveI : Nontrivial (P : Subgroup R) :=
    (Subgroup.nontrivial_iff_ne_bot (H := (P : Subgroup R))).2 hP_ne_bot
  let ZP : Subgroup (P : Subgroup R) := Subgroup.center (P : Subgroup R)
  have hZP_nontrivial : Nontrivial ZP :=
    IsPGroup.center_nontrivial (p := p.val) (G := (P : Subgroup R)) P.isPGroup'
  have hZP_ne_bot : ZP ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (H := ZP)).1 hZP_nontrivial
  let Z : Subgroup R := ZP.map (P : Subgroup R).subtype
  have hZp : IsPGroup p.val Z := by
    have hZPp : IsPGroup p.val ZP := P.isPGroup'.to_subgroup ZP
    exact IsPGroup.map hZPp (P : Subgroup R).subtype
  have hZcomm : IsMulCommutative Z := by
    simpa [Z, ZP] using
      (Subgroup.map_isMulCommutative (f := (P : Subgroup R).subtype)
        (H := Subgroup.center (P : Subgroup R)))
  have hZ_ne_bot : Z ≠ ⊥ := by
    intro hZbot
    have hZP_bot : ZP = ⊥ := by
      apply Subgroup.map_injective (P : Subgroup R).subtype_injective
      simpa [Z] using hZbot
    exact hZP_ne_bot hZP_bot
  haveI : Nontrivial Z :=
    (Subgroup.nontrivial_iff_ne_bot (H := Z)).2 hZ_ne_bot
  exact (section13_one_le_generatorRank_of_nontrivial (R := Z)).trans
    (section13_generatorRank_le_primeRank_of_subgroup (R := R) (q := p.val) hZp hZcomm)

omit [IsMinCE G] in
private theorem CFSG.section13_sylow_inf_normal_ne_bot_of_prime_dvd_normal
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
    rw [hqd]
    exact d.property
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

private theorem CFSG.section13_sylow_le_derived_of_sigma_or_tau3
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section10SigmaPrimes M ∨ p ∈ section12Tau3Primes M)
    (S : Sylow p.val M) :
    (S : Subgroup M) ≤ derivedSubgroup M := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases hp with hpσ | hpτ3
  · exact section10_sigma_sylow_le_derivedSubgroup (G := G) hM hpσ S
  · rcases (by simpa [section12Tau3Primes] using hpτ3) with
      ⟨_hpσ, hpD, hrank⟩
    have hpM : p.val ∣ Nat.card M :=
      hpD.trans (Subgroup.card_subgroup_dvd_card (derivedSubgroup M))
    have hpG : p.val ∣ Nat.card G :=
      hpM.trans (Subgroup.card_subgroup_dvd_card M)
    have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
    have hcyc : IsCyclic (S : Subgroup M) :=
      section10_sylow_isCyclic_of_primeRank_le_one
        (G := G) S hpodd (by omega)
    rcases corollary_1_19_a (G := M) p.val S hcyc with hbot | hle
    · exfalso
      exact section13_sylow_inf_normal_ne_bot_of_prime_dvd_normal
        (R := M) (D := derivedSubgroup M) S hpD hbot
    · exact hle

private theorem CFSG.section13_sigma_or_tau3_of_not_tau12
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpM : p ∈ subgroupPrimeSet M)
    (hpτ1 : p ∉ section12Tau1Primes M)
    (hpτ2 : p ∉ section12Tau2Primes M) :
    p ∈ section10SigmaPrimes M ∨ p ∈ section12Tau3Primes M := by
  classical
  by_cases hpσ : p ∈ section10SigmaPrimes M
  · exact Or.inl hpσ
  · right
    have hpos : 1 ≤ primeRank p.val M :=
      section13_primeRank_pos_of_mem_subgroupPrimeSet (R := M) hpM
    have hle_two : primeRank p.val M ≤ 2 := by
      by_contra hnot
      have hgt : 2 < primeRank p.val M := by omega
      exact hpσ (section13_sigmaPrimes_mem_of_alphaPrimes_mem hM ⟨hpM, hgt⟩)
    have hrank : primeRank p.val M = 1 ∨ primeRank p.val M = 2 := by omega
    rcases hrank with hrank1 | hrank2
    · by_cases hpD : p ∈ subgroupPrimeSet (derivedSubgroup M)
      · simpa [section12Tau3Primes] using ⟨hpσ, hpD, hrank1⟩
      · exfalso
        exact hpτ1 (by simpa [section12Tau1Primes] using ⟨hpσ, hpD, hrank1⟩)
    · exfalso
      exact hpτ2 (by simpa [section12Tau2Primes] using ⟨hpσ, hrank2⟩)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_commutator_le_ambientDerived_of_le
    {M K P : Subgroup G} (hKle : K ≤ M) (hPle : P ≤ M) :
    ⁅K, P⁆ ≤ ambientDerivedSubgroup M := by
  have hcomm_le : ⁅K, P⁆ ≤ ⁅M, M⁆ := Subgroup.commutator_mono hKle hPle
  rw [ambientDerivedSubgroup, derivedSubgroup, derivedSeries_one]
  change ⁅K, P⁆ ≤ (_root_.commutator M).map M.subtype
  rw [Subgroup.map_subtype_commutator]
  exact hcomm_le

private theorem CFSG.section13_not_betaG_of_tau2
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpτ2 : p ∈ section12Tau2Primes M) :
    p ∉ section12BetaPrimesOfGroup G := by
  rcases (by simpa [section12Tau2Primes] using hpτ2) with ⟨hpσ, hrank⟩
  exact by
    simpa [section12BetaPrimesOfGroup] using
      (lemma_10_4_c (G := G) hM hpσ hrank).1

private theorem CFSG.section13_not_beta_of_tau2
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpτ2 : p ∈ section12Tau2Primes M) :
    p ∉ section10BetaPrimes M := by
  intro hpβ
  have hpβG : p ∈ section12BetaPrimesOfGroup G := by
    simpa [section12BetaPrimesOfGroup, section10BetaPrimes] using hpβ.2
  exact section13_not_betaG_of_tau2 (G := G) hM hpτ2 hpβG

private theorem CFSG.section13_not_beta_of_sigma_notconj
    {M Mstar : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hqσ : q ∈ section10SigmaPrimes M) :
    q ∉ section10BetaPrimes Mstar := by
  intro hqβ
  have hdis : Disjoint (section10AlphaPrimes Mstar) (section10SigmaPrimes M) :=
    (lemma_10_12_a (G := G) (M := Mstar) (H := M) hMstar hM
      (section13_notConjugate_symm hnotconj)).2
  rw [Set.disjoint_left] at hdis
  exact hdis hqβ.1 hqσ

private theorem CFSG.section13_ne_of_sigma_and_tau2
    {M E E₁₂ E₁ E₂ E₃ Mstar : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpE : p ∈ subgroupPrimeSet E)
    (hqσ : q ∈ section10SigmaPrimes M)
    (_hpτ2 : p ∈ section12Tau2Primes Mstar) :
    p ≠ q := by
  have hpσM : p ∉ section10SigmaPrimes M :=
    section12_not_sigma_of_mem_complement hM hE.1 hpE
  intro hpq
  exact hpσM (by simpa [hpq] using hqσ)

private theorem CFSG.section13_exists_sigma_prime_in_derived_of_commutator_ne_bot
    {M Mstar : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomm : ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥) :
    ∃ q : Nat.Primes,
      q ∈ section10SigmaPrimes M ∧ q ∈ subgroupPrimeSet (ambientDerivedSubgroup Mstar) := by
  classical
  let C : Subgroup G := ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆
  have hC_ne : C ≠ ⊥ := by simpa [C] using hcomm
  have hC_card_ne_one : Nat.card C ≠ 1 := by
    intro hcard
    exact hC_ne ((Subgroup.card_eq_one (H := C)).1 hcard)
  obtain ⟨q0, hq0prime, hq0C⟩ := Nat.exists_prime_and_dvd hC_card_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  have hqC : q.val ∣ Nat.card C := by simpa [q] using hq0C
  have hC_le_msigma : C ≤ section10Msigma M := by
    have hnorm :
        M ⊓ Mstar ≤ Subgroup.normalizer (section10Msigma M ⊓ Mstar : Set G) :=
      section13_le_normalizer_inf
        (H := section10Msigma M) (K := Mstar)
        (inf_le_left.trans section13_le_normalizer_msigma)
        (inf_le_right.trans Subgroup.le_normalizer)
    exact (section13_commutator_le_left_of_le_normalizer hnorm).trans inf_le_left
  have hC_le_derived : C ≤ ambientDerivedSubgroup Mstar :=
    section13_commutator_le_ambientDerived_of_le
      (M := Mstar) (K := section10Msigma M ⊓ Mstar) (P := M ⊓ Mstar)
      inf_le_right inf_le_right
  have hq_msigma : q.val ∣ Nat.card (section10Msigma M) :=
    hqC.trans (Subgroup.card_dvd_of_le hC_le_msigma)
  have hqσ : q ∈ section10SigmaPrimes M :=
    ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card q hq_msigma
  have hqD : q ∈ subgroupPrimeSet (ambientDerivedSubgroup Mstar) :=
    section8_subgroupPrimeSet_mono hC_le_derived hqC
  exact ⟨q, hqσ, hqD⟩

private theorem CFSG.lemma_13_1_b_core
    {M E E₁₂ E₁ E₂ E₃ Mstar : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hpE : p ∈ subgroupPrimeSet E)
    (_hpMstar : p ∈ subgroupPrimeSet Mstar)
    (_hpτ1star : p ∉ section12Tau1Primes Mstar)
    (hcomm : ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥)
    (hnotconj : section12NotConjugate Mstar M) :
    p ∉ section12Tau2Primes Mstar := by
  classical
  intro hpτ2
  rcases section13_exists_sigma_prime_in_derived_of_commutator_ne_bot
      (G := G) hM hcomm with
    ⟨q, hqσ, hqD⟩
  have hpσstar : p ∉ section10SigmaPrimes Mstar := by
    simpa [section12Tau2Primes] using hpτ2.1
  have hprank : primeRank p.val Mstar = 2 := by
    simpa [section12Tau2Primes] using hpτ2.2
  have hpβG : p ∉ section12BetaPrimesOfGroup G :=
    section13_not_betaG_of_tau2 (G := G) hMstar hpτ2
  have hpβ : p ∉ section10BetaPrimes Mstar :=
    section13_not_beta_of_tau2 (G := G) hMstar hpτ2
  have hqβ : q ∉ section10BetaPrimes Mstar :=
    section13_not_beta_of_sigma_notconj
      (G := G) hM hMstar hnotconj hqσ
  have hpq : p ≠ q :=
    section13_ne_of_sigma_and_tau2
      (G := G) hM hE hpE hqσ hpτ2
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let Dg : Subgroup G := ambientDerivedSubgroup Mstar
  let YS : Sylow q.val Dg := Classical.choice (Sylow.nonempty (p := q.val) (G := Dg))
  let Y : Subgroup G := section10AmbientSylowSubgroup Dg YS
  have hY_ne : Y ≠ ⊥ := by
    have hYS_ne : (YS : Subgroup Dg) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card (G := Dg) YS
        (by simpa [Dg, subgroupPrimeSet] using hqD)
    intro hYbot
    have hYS_bot : (YS : Subgroup Dg) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := (YS : Subgroup Dg)) (f := Dg.subtype)
        Dg.subtype_injective).1 (by simpa [Y, section10AmbientSylowSubgroup] using hYbot)
    exact hYS_ne hYS_bot
  have hYq : IsPGroup q.val Y := by
    change IsPGroup q.val ((YS : Subgroup Dg).map Dg.subtype)
    exact IsPGroup.map (p := q.val) (H := (YS : Subgroup Dg))
      YS.isPGroup' Dg.subtype
  have hYσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Y := by
    intro r hrY
    have hr_singleton : r ∈ ({q} : Set Nat.Primes) :=
      section8_isPiSubgroup_singleton_of_isPGroup hYq r hrY
    have hrq : r = q := by simpa using hr_singleton
    simpa [hrq] using hqσ
  have hDg_le_Mstar : Dg ≤ Mstar := by
    intro x hx
    change x ∈ ambientDerivedSubgroup Mstar at hx
    rw [ambientDerivedSubgroup, Subgroup.mem_map] at hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hY_le_Mstar : Y ≤ Mstar := by
    exact (section13_ambient_sylow_le_base (G := G) Dg YS).trans hDg_le_Mstar
  have hMstar_cont : Mstar ∈ section9MaximalSubgroupsContaining Y :=
    ⟨hMstar, hY_le_Mstar⟩
  have hupper :
      primeRank p.val (subgroupNormalizerIn Mstar (Y : Set G)) ≤ 1 :=
    (corollary_12_16_a
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (Y := Y) (H := Mstar) (p := p)
      hM hE hY_ne hYσ hpE hpβG hMstar_cont hnotconj).2
  have hlower :
      2 ≤ primeRank p.val (subgroupNormalizerIn Mstar (Y : Set G)) := by
    simpa [Y, Dg] using
      section10_primeRank_normalizer_of_derived_sylow_ge_of_not_beta_primeRank
        (G := G) (M := Mstar) (p := p) (q := q)
        hMstar hpβ YS hprank
  omega

omit [Finite G] [IsMinCE G] in
private theorem CFSG.lemma_13_1_a_sylow_cover
    {Mstar P : Subgroup G} {p : Nat.Primes}
    (hPinf : P ≤ Mstar) (hPp : IsPGroup p.val P) :
    ∃ S : Sylow p.val Mstar,
      P ≤ section10Malpha Mstar ⊔ section10AmbientSylowSubgroup Mstar S := by
  classical
  have hPsubp : IsPGroup p.val (P.subgroupOf Mstar) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPinf).symm
  rcases IsPGroup.exists_le_sylow (G := Mstar) (p := p.val) hPsubp with
    ⟨S, hPsubS⟩
  refine ⟨S, ?_⟩
  intro x hx
  have hxS : x ∈ section10AmbientSylowSubgroup Mstar S :=
    Subgroup.mem_map.mpr
      ⟨⟨x, hPinf hx⟩, hPsubS (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  exact (show section10AmbientSylowSubgroup Mstar S ≤
    section10Malpha Mstar ⊔ section10AmbientSylowSubgroup Mstar S from le_sup_right) hxS

private theorem CFSG.lemma_13_1_a_malpha_sylow_normalized
    {Mstar : Subgroup G} {p : Nat.Primes} (S : Sylow p.val Mstar)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hpMstar : p ∈ subgroupPrimeSet Mstar)
    (hpτ1star : p ∉ section12Tau1Primes Mstar)
    (hpτ2star : p ∉ section12Tau2Primes Mstar) :
    Mstar ≤ Subgroup.normalizer
      ((section10Malpha Mstar ⊔ section10AmbientSylowSubgroup Mstar S :
        Subgroup G) : Set G) := by
  have hp_location :
      p ∈ section10SigmaPrimes Mstar ∨ p ∈ section12Tau3Primes Mstar :=
    section13_sigma_or_tau3_of_not_tau12
      (G := G) hMstar hpMstar hpτ1star hpτ2star
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hSleD : (S : Subgroup Mstar) ≤ derivedSubgroup Mstar :=
    section13_sylow_le_derived_of_sigma_or_tau3 (G := G) hMstar hp_location S
  let D : Subgroup Mstar := derivedSubgroup Mstar
  let Dg : Subgroup G := ambientDerivedSubgroup Mstar
  let SD : Sylow p.val D := S.subtype hSleD
  let e : D ≃* Dg := by
    change D ≃* D.map Mstar.subtype
    exact Subgroup.equivMapOfInjective
      (f := Mstar.subtype) D Mstar.subtype_injective
  let X : Sylow p.val Dg := SD.mapSurjective (f := e.toMonoidHom) e.surjective
  have hXsub_eq :
      (section10AmbientSylowSubgroup Dg X).subgroupOf Mstar = (S : Subgroup Mstar) := by
    ext x
    constructor
    · intro hx
      change ((x : Mstar) : G) ∈ section10AmbientSylowSubgroup Dg X at hx
      rw [section10AmbientSylowSubgroup, Subgroup.mem_map] at hx
      rcases hx with ⟨yDg, hyX, hyx⟩
      have hyX' : yDg ∈ (SD : Subgroup D).map e.toMonoidHom := by
        simpa [X, Sylow.coe_mapSurjective] using hyX
      rcases Subgroup.mem_map.mp hyX' with ⟨yD, hySD, hyD_eq⟩
      have hx_eq : x = ((yD : D) : Mstar) := by
        apply Subtype.ext
        calc
          (x : G) = (yDg : G) := hyx.symm
          _ = (e yD : G) := by exact congrArg Subtype.val hyD_eq.symm
          _ = (((yD : D) : Mstar) : G) := by
            unfold e
            exact Subgroup.coe_equivMapOfInjective_apply
              D Mstar.subtype Mstar.subtype_injective yD
      have hyS : ((yD : D) : Mstar) ∈ (S : Subgroup Mstar) := by
        simpa [SD, Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hySD
      simpa [hx_eq] using hyS
    · intro hx
      have hxD : x ∈ D := hSleD hx
      let yD : D := ⟨x, hxD⟩
      have hySD : yD ∈ (SD : Subgroup D) := by
        simpa [SD, Sylow.coe_subtype, yD, Subgroup.mem_subgroupOf] using hx
      have hyX : e yD ∈ (X : Subgroup Dg) := by
        simpa [X, Sylow.coe_mapSurjective] using
          (show e yD ∈ (SD : Subgroup D).map e.toMonoidHom from
            ⟨yD, hySD, rfl⟩)
      change ((x : Mstar) : G) ∈ section10AmbientSylowSubgroup Dg X
      rw [section10AmbientSylowSubgroup, Subgroup.mem_map]
      refine ⟨e yD, hyX, ?_⟩
      unfold e
      exact Subgroup.coe_equivMapOfInjective_apply
        D Mstar.subtype Mstar.subtype_injective yD
  have hlocal_normal :
      (section10MalphaSubgroup Mstar ⊔ (S : Subgroup Mstar)).Normal := by
    have h :=
      section10_malpha_sup_ambient_derived_sylow_normal
        (G := G) (M := Mstar) hMstar X
    simpa [Dg, hXsub_eq] using h
  let L : Subgroup Mstar := section10MalphaSubgroup Mstar ⊔ (S : Subgroup Mstar)
  haveI : L.Normal := by simpa [L] using hlocal_normal
  have hnorm :
      Mstar ≤ Subgroup.normalizer (L.map Mstar.subtype : Set G) :=
    section13_map_subtype_le_normalizer_of_normal Mstar L
  simpa [L, section10Malpha, section10AmbientSylowSubgroup, Subgroup.map_sup] using hnorm

private theorem CFSG.lemma_13_1_a_malpha_sylow_support
    {Mstar P : Subgroup G} {p : Nat.Primes}
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hpMstar : p ∈ subgroupPrimeSet Mstar)
    (hpτ1star : p ∉ section12Tau1Primes Mstar)
    (hpτ2star : p ∉ section12Tau2Primes Mstar)
    (hPinf : P ≤ Mstar) (hPp : IsPGroup p.val P) :
    ∃ S : Sylow p.val Mstar,
      P ≤ section10Malpha Mstar ⊔ section10AmbientSylowSubgroup Mstar S ∧
        Mstar ≤ Subgroup.normalizer
          ((section10Malpha Mstar ⊔ section10AmbientSylowSubgroup Mstar S :
            Subgroup G) : Set G) := by
  rcases lemma_13_1_a_sylow_cover (G := G) (Mstar := Mstar) (P := P) (p := p)
      hPinf hPp with
    ⟨S, hPS⟩
  exact ⟨S, hPS,
    lemma_13_1_a_malpha_sylow_normalized
      (G := G) S hMstar hpMstar hpτ1star hpτ2star⟩

private theorem CFSG.lemma_13_1_a_commutator_le_sigma_compl
    {M E E₁₂ E₁ E₂ E₃ Mstar P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hpE : p ∈ subgroupPrimeSet E)
    (hpMstar : p ∈ subgroupPrimeSet Mstar)
    (hpτ1star : p ∉ section12Tau1Primes Mstar)
    (hcomm : ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥)
    (hnotconj : section12NotConjugate Mstar M)
    (hPinf : P ≤ M ⊓ Mstar) (hPp : IsPGroup p.val P) :
    ∃ L : Subgroup G,
      IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ L ∧
        ⁅section10Msigma M ⊓ Mstar, P⁆ ≤ L := by
  classical
  have hpσM : p ∉ section10SigmaPrimes M :=
    section12_not_sigma_of_mem_complement hM hE.1 hpE
  have hpτ2star : p ∉ section12Tau2Primes Mstar :=
    lemma_13_1_b_core (G := G) hM hE hMstar hpE hpMstar hpτ1star hcomm hnotconj
  have hPstar : P ≤ Mstar := hPinf.trans inf_le_right
  rcases lemma_13_1_a_malpha_sylow_support
      (G := G) (Mstar := Mstar) (P := P) (p := p)
      hMstar hpMstar hpτ1star hpτ2star hPstar hPp with
    ⟨S, hPL, hMstar_normL⟩
  let L : Subgroup G := section10Malpha Mstar ⊔ section10AmbientSylowSubgroup Mstar S
  have hAlphaπ :
      IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ (section10Malpha Mstar) :=
    section13_malpha_isPiSubgroup_sigma_compl_of_notconj
      (G := G) hMstar hM hnotconj
  have hSπ :
      IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ
        (section10AmbientSylowSubgroup Mstar S) :=
    section13_ambient_sylow_isPiSubgroup_sigma_compl_of_not_sigma
      (G := G) (M := M) (Mstar := Mstar) hpσM S
  have hSnormAlpha :
      section10AmbientSylowSubgroup Mstar S ≤
        Subgroup.normalizer (section10Malpha Mstar : Set G) :=
    (section13_ambient_sylow_le_base (G := G) Mstar S).trans
      section13_le_normalizer_malpha
  have hLπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ L := by
    have hsup :
        IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ
          (section10AmbientSylowSubgroup Mstar S ⊔ section10Malpha Mstar) :=
      section13_isPiSubgroup_sup_of_le_normalizer
        (G := G) (π := (section10SigmaPrimes M)ᶜ)
        hSπ hAlphaπ hSnormAlpha
    simpa [L, sup_comm] using hsup
  refine ⟨L, hLπ, ?_⟩
  have hKstar : section10Msigma M ⊓ Mstar ≤ Mstar := inf_le_right
  have hKnormL :
      section10Msigma M ⊓ Mstar ≤ Subgroup.normalizer (L : Set G) :=
    hKstar.trans (by simpa [L] using hMstar_normL)
  exact section13_commutator_le_right_of_le_normalizer hKnormL (by simpa [L] using hPL)

/-- Lemma 13.1(a): under the stated hypotheses, every `p`-subgroup of
`M ∩ M*` centralizes `M_σ ∩ M*`. -/
public theorem CFSG.lemma_13_1_a
    {M E E₁₂ E₁ E₂ E₃ Mstar : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hpE : p ∈ subgroupPrimeSet E)
    (hpMstar : p ∈ subgroupPrimeSet Mstar)
    (hpτ1star : p ∉ section12Tau1Primes Mstar)
    (hcomm : ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥)
    (hnotconj : section12NotConjugate Mstar M) :
    ∀ P : Subgroup G, P ≤ M ⊓ Mstar → IsPGroup p.val P →
      P ≤ Subgroup.centralizer (section10Msigma M ⊓ Mstar : Set G) := by
  classical
  intro P hPinf hPp
  let K : Subgroup G := section10Msigma M ⊓ Mstar
  have hPnormK : P ≤ Subgroup.normalizer (K : Set G) := by
    have hPM : P ≤ M := hPinf.trans inf_le_left
    have hPMstar : P ≤ Mstar := hPinf.trans inf_le_right
    simpa [K] using
      section13_le_normalizer_inf
        (H := section10Msigma M) (K := Mstar)
        (hPM.trans section13_le_normalizer_msigma)
        (hPMstar.trans Subgroup.le_normalizer)
  have hKπ : IsPiSubgroup (G := G) (section10SigmaPrimes M) K := by
    have hMσπ :
        IsPiSubgroup (G := G) (section10SigmaPrimes M) (section10Msigma M) := by
      intro q hq
      exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card q hq
    exact IsPiSubgroup.of_le (H := K) inf_le_left hMσπ
  rcases lemma_13_1_a_commutator_le_sigma_compl
      (G := G) hM hE hMstar hpE hpMstar hpτ1star hcomm hnotconj
      hPinf hPp with
    ⟨L, hLπc, hcommL⟩
  simpa [K] using
    section13_centralizes_of_commutator_le_pi_compl
      (G := G) (π := section10SigmaPrimes M) (K := K) (P := P) (L := L)
      hPnormK hKπ hLπc (by simpa [K] using hcommL)

/-- Lemma 13.1(b): under the stated hypotheses, `p ∉ τ₂(M*)`. -/
public theorem CFSG.lemma_13_1_b
    {M E E₁₂ E₁ E₂ E₃ Mstar : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hpE : p ∈ subgroupPrimeSet E)
    (hpMstar : p ∈ subgroupPrimeSet Mstar)
    (hpτ1star : p ∉ section12Tau1Primes Mstar)
    (hcomm : ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥)
    (hnotconj : section12NotConjugate Mstar M) :
    p ∉ section12Tau2Primes Mstar := by
  exact lemma_13_1_b_core (G := G) hM hE hMstar hpE hpMstar hpτ1star hcomm hnotconj

public theorem CFSG.section13_ne_of_sigma_and_mem_E
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpE : p ∈ subgroupPrimeSet E)
    (hqσ : q ∈ section10SigmaPrimes M) :
    p ≠ q := by
  have hpσM : p ∉ section10SigmaPrimes M :=
    section12_not_sigma_of_mem_complement hM hE.1 hpE
  intro hpq
  exact hpσM (by simpa [hpq] using hqσ)

private theorem CFSG.section13_prime_mem_ambientDerived_of_sigma_or_tau3
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpM : p ∈ subgroupPrimeSet M)
    (hp : p ∈ section10SigmaPrimes M ∨ p ∈ section12Tau3Primes M) :
    p ∈ subgroupPrimeSet (ambientDerivedSubgroup M) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let S : Sylow p.val M := Classical.choice (Sylow.nonempty (p := p.val) (G := M))
  have hS_ne : (S : Subgroup M) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := M) S hpM
  have hSleD : (S : Subgroup M) ≤ derivedSubgroup M :=
    section13_sylow_le_derived_of_sigma_or_tau3 (G := G) hM hp S
  let SG : Subgroup G := section10AmbientSylowSubgroup M S
  have hSG_le_Dg : SG ≤ ambientDerivedSubgroup M := by
    intro x hx
    change x ∈ section10AmbientSylowSubgroup M S at hx
    rw [section10AmbientSylowSubgroup, Subgroup.mem_map] at hx
    rcases hx with ⟨s, hs, rfl⟩
    exact Subgroup.mem_map_of_mem M.subtype (hSleD hs)
  have hSG_ne : SG ≠ ⊥ := by
    intro hSG_bot
    have hS_bot : (S : Subgroup M) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := (S : Subgroup M)) (f := M.subtype)
        M.subtype_injective).1 (by simpa [SG, section10AmbientSylowSubgroup] using hSG_bot)
    exact hS_ne hS_bot
  have hSGp : IsPGroup p.val SG := by
    change IsPGroup p.val ((S : Subgroup M).map M.subtype)
    exact IsPGroup.map (p := p.val) (H := (S : Subgroup M))
      S.isPGroup' M.subtype
  exact section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
    (A := ambientDerivedSubgroup M) (B := SG.subgroupOf (ambientDerivedSubgroup M))
    (hBp := hSGp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := SG) (K := ambientDerivedSubgroup M)
        hSG_le_Dg).symm)
    (hB_ne_bot := by
      intro hbot
      exact hSG_ne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hSG_le_Dg))

private theorem CFSG.section13_prime_mem_derived_normalizer_of_not_betaG
    {M E E₁₂ E₁ E₂ E₃ Mstar : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hpE : p ∈ subgroupPrimeSet E)
    (hpMstar : p ∈ subgroupPrimeSet Mstar)
    (hp_location : p ∈ section10SigmaPrimes Mstar ∨ p ∈ section12Tau3Primes Mstar)
    (hpβG : p ∉ section12BetaPrimesOfGroup G)
    (hqσ : q ∈ section10SigmaPrimes M)
    (hqD : q ∈ subgroupPrimeSet (ambientDerivedSubgroup Mstar))
    (hnotconj : section12NotConjugate Mstar M)
    (Y : Sylow q.val (ambientDerivedSubgroup Mstar)) :
    p ∈ subgroupPrimeSet
      (ambientDerivedSubgroup
        (subgroupNormalizerIn Mstar
          (section10AmbientSylowSubgroup (ambientDerivedSubgroup Mstar) Y : Set G))) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let Dg : Subgroup G := ambientDerivedSubgroup Mstar
  have hpDg : p ∈ subgroupPrimeSet Dg :=
    by simpa [Dg] using
      section13_prime_mem_ambientDerived_of_sigma_or_tau3
        (G := G) hMstar hpMstar hp_location
  have hDg_le_Mstar : Dg ≤ Mstar := by
    intro x hx
    change x ∈ ambientDerivedSubgroup Mstar at hx
    rw [ambientDerivedSubgroup, Subgroup.mem_map] at hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hqMstar : q ∈ subgroupPrimeSet Mstar :=
    section8_subgroupPrimeSet_mono hDg_le_Mstar (by simpa [Dg] using hqD)
  have hpβstar : p ∉ section10BetaPrimes Mstar := by
    intro hpβstar
    have hpβG' : p ∈ section12BetaPrimesOfGroup G := by
      simpa [section12BetaPrimesOfGroup, section10BetaPrimes] using hpβstar.2
    exact hpβG hpβG'
  have hqβstar : q ∉ section10BetaPrimes Mstar :=
    section13_not_beta_of_sigma_notconj
      (G := G) hM hMstar hnotconj hqσ
  have hpq : p ≠ q :=
    section13_ne_of_sigma_and_mem_E
      (G := G) hM hE hpE hqσ
  obtain ⟨P, hP_le_DU⟩ :=
    corollary_10_9_a_3
      (G := G) (M := Mstar) (p := p) (q := q)
      hMstar hpMstar hqMstar hpβstar hqβstar hpq Y
  let DU : Subgroup G :=
    ambientDerivedSubgroup
      (subgroupNormalizerIn Mstar
        (section10AmbientSylowSubgroup Dg Y : Set G))
  let PG : Subgroup G := section10AmbientSylowSubgroup Dg P
  have hPG_le_DU : PG ≤ DU := by
    simpa [PG, DU, Dg] using hP_le_DU
  have hP_ne : (P : Subgroup Dg) ≠ ⊥ := by
    have hpDg' : p.val ∣ Nat.card Dg := by
      change p.val ∣ Nat.card (ambientDerivedSubgroup Mstar)
      exact hpDg
    exact Sylow.ne_bot_of_dvd_card (G := Dg) P hpDg'
  have hPG_ne : PG ≠ ⊥ := by
    intro hPG_bot
    have hP_bot : (P : Subgroup Dg) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := (P : Subgroup Dg)) (f := Dg.subtype)
        Dg.subtype_injective).1 (by simpa [PG, section10AmbientSylowSubgroup] using hPG_bot)
    exact hP_ne hP_bot
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val ((P : Subgroup Dg).map Dg.subtype)
    exact IsPGroup.map (p := p.val) (H := (P : Subgroup Dg))
      P.isPGroup' Dg.subtype
  simpa [DU, Dg] using
    section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
      (A := DU) (B := PG.subgroupOf DU)
      (hBp := hPGp.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := PG) (K := DU) hPG_le_DU).symm)
      (hB_ne_bot := by
        intro hbot
        exact hPG_ne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hPG_le_DU))

/-- Lemma 13.1(c): under the stated hypotheses, if `p ∈ τ₁(M)`, then
`p ∈ β(G)`. -/
public theorem CFSG.lemma_13_1_c
    {M E E₁₂ E₁ E₂ E₃ Mstar : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hpE : p ∈ subgroupPrimeSet E)
    (hpMstar : p ∈ subgroupPrimeSet Mstar)
    (hpτ1star : p ∉ section12Tau1Primes Mstar)
    (hcomm : ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥)
    (hnotconj : section12NotConjugate Mstar M)
    (hpτ1 : p ∈ section12Tau1Primes M) :
    p ∈ section12BetaPrimesOfGroup G := by
  classical
  by_contra hpβG
  have hpτ2star : p ∉ section12Tau2Primes Mstar :=
    lemma_13_1_b_core (G := G) hM hE hMstar hpE hpMstar hpτ1star hcomm hnotconj
  have hp_location :
      p ∈ section10SigmaPrimes Mstar ∨ p ∈ section12Tau3Primes Mstar :=
    section13_sigma_or_tau3_of_not_tau12
      (G := G) hMstar hpMstar hpτ1star hpτ2star
  rcases section13_exists_sigma_prime_in_derived_of_commutator_ne_bot
      (G := G) hM hcomm with
    ⟨q, hqσ, hqD⟩
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let Dg : Subgroup G := ambientDerivedSubgroup Mstar
  let YS : Sylow q.val Dg := Classical.choice (Sylow.nonempty (p := q.val) (G := Dg))
  let Y : Subgroup G := section10AmbientSylowSubgroup Dg YS
  have hY_ne : Y ≠ ⊥ := by
    have hYS_ne : (YS : Subgroup Dg) ≠ ⊥ :=
      by
        have hqD' : q.val ∣ Nat.card Dg := by
          change q.val ∣ Nat.card (ambientDerivedSubgroup Mstar)
          exact hqD
        exact Sylow.ne_bot_of_dvd_card (G := Dg) YS hqD'
    intro hYbot
    have hYS_bot : (YS : Subgroup Dg) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := (YS : Subgroup Dg)) (f := Dg.subtype)
        Dg.subtype_injective).1 (by simpa [Y, section10AmbientSylowSubgroup] using hYbot)
    exact hYS_ne hYS_bot
  have hYq : IsPGroup q.val Y := by
    change IsPGroup q.val ((YS : Subgroup Dg).map Dg.subtype)
    exact IsPGroup.map (p := q.val) (H := (YS : Subgroup Dg))
      YS.isPGroup' Dg.subtype
  have hYσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Y := by
    intro r hrY
    have hr_singleton : r ∈ ({q} : Set Nat.Primes) :=
      section8_isPiSubgroup_singleton_of_isPGroup hYq r hrY
    have hrq : r = q := by simpa using hr_singleton
    simpa [hrq] using hqσ
  have hDg_le_Mstar : Dg ≤ Mstar := by
    intro x hx
    change x ∈ ambientDerivedSubgroup Mstar at hx
    rw [ambientDerivedSubgroup, Subgroup.mem_map] at hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hY_le_Mstar : Y ≤ Mstar := by
    exact (section13_ambient_sylow_le_base (G := G) Dg YS).trans hDg_le_Mstar
  have hMstar_cont : Mstar ∈ section9MaximalSubgroupsContaining Y :=
    ⟨hMstar, hY_le_Mstar⟩
  have hnot_support :
      p ∉ subgroupPrimeSet
        (ambientDerivedSubgroup (subgroupNormalizerIn Mstar (Y : Set G))) :=
    (corollary_12_16_b
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (Y := Y) (H := Mstar) (p := p)
      hM hE hY_ne hYσ hpE hpβG hMstar_cont hnotconj hpτ1).2
  have hsupport :
      p ∈ subgroupPrimeSet
        (ambientDerivedSubgroup (subgroupNormalizerIn Mstar (Y : Set G))) := by
    simpa [Y, Dg] using
      section13_prime_mem_derived_normalizer_of_not_betaG
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (Mstar := Mstar) (p := p) (q := q)
        hM hE hMstar hpE hpMstar hp_location hpβG hqσ hqD hnotconj YS
  exact hnot_support hsupport

end Section13
