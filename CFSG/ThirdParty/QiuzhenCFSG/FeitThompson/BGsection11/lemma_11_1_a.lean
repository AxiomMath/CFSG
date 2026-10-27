module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.Defs
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

/-!
# Statements from BG Section 11

This file records the statement-only scaffold for Section 11 of
`Local Analysis for the Odd Order Theorem`.
-/

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_isElementaryAbelian_zpowers_of_pow_eq_one
    {p : ℕ} [Fact p.Prime] {x : G} (hxpow : x ^ p = 1) :
    IsElementaryAbelian p (Subgroup.zpowers x) := by
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro y
  apply Subtype.ext
  have hy_dvd : orderOf ((y : Subgroup.zpowers x) : G) ∣ p := by
    exact (orderOf_dvd_of_mem_zpowers y.2).trans (orderOf_dvd_of_pow_eq_one hxpow)
  simpa using (orderOf_dvd_iff_pow_eq_one.mp hy_dvd)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_isElementaryAbelian_sup_of_le_centralizer
    {p : ℕ} [Fact p.Prime] {E C : Subgroup G}
    [IsElementaryAbelian p E] [IsElementaryAbelian p C]
    (hCE : C ≤ Subgroup.centralizer (E : Set G)) :
    IsElementaryAbelian p ↥(E ⊔ C) := by
  classical
  let s : Set G := (E : Set G) ∪ (C : Set G)
  have hcomm_s : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    rcases hx with hxE | hxC
    · rcases hy with hyE | hyC
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := E)).comm ⟨x, hxE⟩ ⟨y, hyE⟩)
      · exact (Subgroup.mem_centralizer_iff.mp (hCE hyC)) x hxE
    · rcases hy with hyE | hyC
      · exact ((Subgroup.mem_centralizer_iff.mp (hCE hxC)) y hyE).symm
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := C)).comm ⟨x, hxC⟩ ⟨y, hyC⟩)
  have hsup : E ⊔ C = Subgroup.closure s := by
    simpa [s] using (Subgroup.sup_eq_closure E C)
  refine
    { toIsMulCommutative := by
        rw [hsup]
        exact Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm_s x hx y hy
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  have hxcl : (x : G) ∈ Subgroup.closure s := by
    simpa [hsup] using x.property
  exact
    Subgroup.closure_induction (k := s)
      (p := fun z hz => z ^ p = 1) (x := (x : G)) (by
        intro y hy
        rcases hy with hyE | hyC
        · have hypow : (⟨y, hyE⟩ : E) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p E) ⟨y, hyE⟩
          simpa using congrArg Subtype.val hypow
        · have hypow : (⟨y, hyC⟩ : C) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p C) ⟨y, hyC⟩
          simpa using congrArg Subtype.val hypow) (by simp) (by
        intro y z hy hz hypow hzpow
        have hyz_comm : Commute y z := by
          have hclosure_comm : IsMulCommutative ↥(Subgroup.closure s) :=
            Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm_s x hx y hy
          show y * z = z * y
          simpa using congrArg Subtype.val
            (hclosure_comm.is_comm.comm
              (⟨y, hy⟩ : Subgroup.closure s) (⟨z, hz⟩ : Subgroup.closure s))
        calc
          (y * z) ^ p = y ^ p * z ^ p := by simpa using hyz_comm.mul_pow p
          _ = 1 := by simp [hypow, hzpow]) (by
        intro y hy hypow
        simpa [inv_pow] using congrArg Inv.inv hypow) hxcl

omit [IsMinCE G] in
public theorem CFSG.section11Data.A_ne_bot
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    A ≠ ⊥ := by
  have hAcard : Nat.card A = p.val ^ 2 := h11.A_rank_two.1
  intro hAbot
  have hcard1 : Nat.card A = 1 := by simp [hAbot]
  have hp1 : p.val ^ 2 = 1 := hAcard.symm.trans hcard1
  have hpgt : 1 < p.val ^ 2 := Nat.one_lt_pow (by decide : 2 ≠ 0) p.2.one_lt
  omega

omit [IsMinCE G] in
public theorem CFSG.section11Data.A_eq_centralizer_p_elements
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    (A : Set G) =
      {x : G | x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p.val = 1} := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases h11.rankTwoMaximal with ⟨hArank, hAmax⟩
  rcases hArank with ⟨_hAcard, hAelem⟩
  rcases hAmax with ⟨_hAelem', hAmaximal⟩
  letI : IsElementaryAbelian p.val A := hAelem
  ext x
  constructor
  · intro hxA
    refine ⟨?_, elemPow_eq_one_of_isElementaryAbelian x hxA⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hyA
    exact (congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := A)).comm ⟨x, hxA⟩ ⟨y, hyA⟩)
      ).symm
  · rintro ⟨hxcent, hxpow⟩
    let Z : Subgroup G := Subgroup.zpowers x
    have hZelem : IsElementaryAbelian p.val Z :=
      section11_isElementaryAbelian_zpowers_of_pow_eq_one (p := p.val) (x := x) hxpow
    letI : IsElementaryAbelian p.val Z := hZelem
    have hZ_le_centA : Z ≤ Subgroup.centralizer (A : Set G) :=
      (Subgroup.zpowers_le).2 hxcent
    have hsup_elem : IsElementaryAbelian p.val ↥(A ⊔ Z) :=
      section11_isElementaryAbelian_sup_of_le_centralizer
        (p := p.val) (E := A) (C := Z) hZ_le_centA
    have hsup_eq : A = A ⊔ Z :=
      hAmaximal (A ⊔ Z) le_sup_left hsup_elem
    have hx_sup : x ∈ A ⊔ Z := by
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rw [← hsup_eq] at hx_sup
    exact hx_sup

public theorem CFSG.section11Data.hypothesis7_1
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    Hypothesis7_1 A := by
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases h11.A_rank_two with ⟨hAcard, hAelem⟩
  letI : IsElementaryAbelian p.val A := hAelem
  have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
  letI : IsMulCommutative A := hAelem.toIsMulCommutative
  have hpA : p.val ∣ Nat.card A := by
    rw [hAcard, pow_two]
    exact dvd_mul_right p.val p.val
  have hpG : p.val ∣ Nat.card G :=
    hpA.trans (Subgroup.card_subgroup_dvd_card A)
  refine proposition_7_5 (G := G) (p := p.val) hpG hAp (Or.inl ?_)
  exact ⟨h11.A_eq_centralizer_p_elements, fun X hXproper =>
    theorem_10_6 (G := G) (p := p) hXproper⟩

omit [IsMinCE G] in
public theorem CFSG.section11Data.A_subgroupPrimeSet_eq_singleton
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    subgroupPrimeSet A = ({p} : Set Nat.Primes) := by
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases h11.A_rank_two with ⟨_hAcard, hAelem⟩
  letI : IsElementaryAbelian p.val A := hAelem
  exact section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
    (IsElementaryAbelian.isPGroup p.val A) h11.A_ne_bot

omit [IsMinCE G] in
public theorem CFSG.section11Data.q_not_mem_A_primeSet
    {M A0 A : Subgroup G} {p q : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) (hqσ : q ∈ section10SigmaPrimes M) :
    q ∉ subgroupPrimeSet A := by
  intro hqA
  have hqmem : q ∈ ({p} : Set Nat.Primes) := by
    simpa [h11.A_subgroupPrimeSet_eq_singleton] using hqA
  have hqp : q = p := by simpa using hqmem
  exact h11.not_sigma (by simpa [hqp] using hqσ)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_msigma_le
    (M : Subgroup G) :
    section10Msigma M ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.2

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_ambientSylow_le
    {q : Nat.Primes} (H : Subgroup G) (Q : Sylow q.val H) :
    section10AmbientSylowSubgroup H Q ≤ H := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.2

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_ambientSylow_isPGroup
    {q : Nat.Primes} (H : Subgroup G) (Q : Sylow q.val H) :
    IsPGroup q.val (section10AmbientSylowSubgroup H Q) := by
  change IsPGroup q.val ((Q : Subgroup H).map H.subtype)
  exact IsPGroup.map (p := q.val) (H := (Q : Subgroup H)) Q.isPGroup' H.subtype


omit [IsMinCE G] in
public theorem CFSG.section11_ambientSylow_isSylow_of_hall
    {H K : Subgroup G} {π : Set Nat.Primes} {q : Nat.Primes}
    (hHall : IsHallSubgroup π K) (hqπ : q ∈ π) (hKH : K ≤ H)
    (Q : Sylow q.val K) :
    ∃ S : Sylow q.val H,
      section10AmbientSylowSubgroup H S = section10AmbientSylowSubgroup K Q := by
  classical
  haveI : Fact q.val.Prime := ⟨q.2⟩
  have hQamb_le_H : section10AmbientSylowSubgroup K Q ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact hKH y.2
  let R : Subgroup H := (section10AmbientSylowSubgroup K Q).subgroupOf H
  have hR_p : IsPGroup q.val R := by
    have hRG : IsPGroup q.val (section10AmbientSylowSubgroup K Q) :=
      section11_ambientSylow_isPGroup K Q
    exact hRG.of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (H := section10AmbientSylowSubgroup K Q) (K := H) hQamb_le_H).symm
  have hR_map : R.map H.subtype = section10AmbientSylowSubgroup K Q := by
    simp [R, inf_eq_left.2 hQamb_le_H]
  have hR_not_dvd : ¬ q.val ∣ R.index := by
    intro hidx
    have hidx_map :
        (section10AmbientSylowSubgroup K Q).index = R.index * H.index := by
      have := Subgroup.index_map_subtype (H := H) (K := R)
      simpa [hR_map] using this
    have hq_dvd_indexG :
        q.val ∣ (section10AmbientSylowSubgroup K Q).index := by
      rw [hidx_map]
      exact dvd_mul_of_dvd_left hidx H.index
    have hidx2 :
        (section10AmbientSylowSubgroup K Q).index =
          (Q : Subgroup K).index * K.index := by
      simpa [section10AmbientSylowSubgroup] using
        Subgroup.index_map_subtype (H := K) (K := (Q : Subgroup K))
    have hq_dvd_mul : q.val ∣ (Q : Subgroup K).index * K.index := by
      simpa [hidx2] using hq_dvd_indexG
    rcases q.2.dvd_mul.mp hq_dvd_mul with hqQ | hqK
    · exact Q.not_dvd_index hqQ
    · exact (hHall.p_in_pi_of_p_dvd_index q hqK) hqπ
  let S : Sylow q.val H := IsPGroup.toSylow (p := q.val) hR_p hR_not_dvd
  refine ⟨S, ?_⟩
  calc
    section10AmbientSylowSubgroup H S = R.map H.subtype := by
      simp [S, section10AmbientSylowSubgroup]
    _ = section10AmbientSylowSubgroup K Q := hR_map

omit [IsMinCE G] in
public theorem CFSG.section11_normalizer_ambientSylow_le_of_sigma
    {M : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hqσ : q ∈ section10SigmaPrimes M)
    (S : Sylow q.val M) :
    Subgroup.normalizer (section10AmbientSylowSubgroup M S : Set G) ≤ M := by
  intro x hx
  exact theorem_10_1_d hM hqσ S (g := x) (by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    exact section11_ambientSylow_le M S
      ((Subgroup.mem_normalizer_iff.mp hx z).1 hz))

public theorem CFSG.section11_normalizer_ne_top_of_ne_bot_ne_top
    {Q : Subgroup G} (hQ_ne_bot : Q ≠ ⊥) (hQ_ne_top : Q ≠ ⊤) :
    Subgroup.normalizer (Q : Set G) ≠ ⊤ := by
  intro hNtop
  have hQnormal : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  letI : IsSimpleGroup G := IsMinCE.simple
  rcases hQnormal.eq_bot_or_eq_top with hQbot | hQtop
  · exact hQ_ne_bot hQbot
  · exact hQ_ne_top hQtop

public theorem CFSG.section11_centralizer_ne_top_of_prime_order
    {X : Subgroup G} {p : Nat.Primes} (hXcard : Nat.card X = p.val) :
    Subgroup.centralizer (X : Set G) ≠ ⊤ := by
  intro hCtop
  have hX_ne_bot : X ≠ ⊥ := by
    intro hXbot
    have hcard1 : Nat.card X = 1 := by simp [hXbot]
    have hp1 : p.val = 1 := by
      rw [← hXcard]
      exact hcard1
    exact p.2.not_dvd_one (by simp [hp1])
  have hX_le_center : X ≤ Subgroup.center G := by
    have hsubset : (X : Set G) ⊆ Subgroup.center G :=
      (Subgroup.centralizer_eq_top_iff_subset).mp hCtop
    intro x hx
    exact hsubset hx
  have hcenter_ne_bot : Subgroup.center G ≠ ⊥ :=
    ne_bot_of_le_ne_bot hX_ne_bot hX_le_center
  exact hcenter_ne_bot (center_eq_bot_of_min_ce (G := G))

omit [IsMinCE G] in
public theorem CFSG.section11_star_of_ambient_sylow_normalizer_le
    {K A R : Subgroup G} {q : Nat.Primes} (S : Sylow q.val K)
    (hS_eq : section10AmbientSylowSubgroup K S = R)
    (hAnorm : A ≤ Subgroup.normalizer (R : Set G))
    (hnormR_le_K : Subgroup.normalizer (R : Set G) ≤ K) :
    R ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
  classical
  haveI : Fact q.val.Prime := ⟨q.2⟩
  have hR_q : IsPGroup q.val R := by
    have htmp : IsPGroup q.val (section10AmbientSylowSubgroup K S) :=
      section11_ambientSylow_isPGroup K S
    rw [hS_eq] at htmp
    exact htmp
  have hRπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) R :=
    section8_isPiSubgroup_singleton_of_isPGroup hR_q
  refine ⟨⟨le_top, hRπ, hAnorm⟩, ?_⟩
  intro T hRT hTfam
  by_contra hT_ne_R
  have hnot_T_le_R : ¬ T ≤ R := by
    intro hTR
    exact hT_ne_R (le_antisymm hRT hTR).symm
  have hRsub_ne_top : R.subgroupOf T ≠ ⊤ := by
    intro htop
    have hTR : T ≤ R := Subgroup.subgroupOf_eq_top.mp htop
    exact hnot_T_le_R hTR
  have hRsub_lt_top : R.subgroupOf T < ⊤ :=
    lt_top_iff_ne_top.mpr hRsub_ne_top
  have hT_q : IsPGroup q.val T :=
    section8_isPGroup_of_isPiSubgroup_singleton hTfam.2.1
  haveI : Group.IsNilpotent T :=
    IsPGroup.isNilpotent (p := q.val) (G := T) hT_q
  have hnc : NormalizerCondition T := Group.normalizerCondition_of_isNilpotent (G := T)
  let Nsub : Subgroup T :=
    Subgroup.normalizer ((R.subgroupOf T : Subgroup T) : Set T)
  have hRsub_lt_N : R.subgroupOf T < Nsub :=
    hnc (R.subgroupOf T) hRsub_lt_top
  let Namb : Subgroup G := Nsub.map T.subtype
  have hR_le_Namb : R ≤ Namb := by
    intro x hx
    refine Subgroup.mem_map.mpr ?_
    refine ⟨⟨x, hRT hx⟩, ?_, rfl⟩
    exact Subgroup.le_normalizer
      (show (⟨x, hRT hx⟩ : T) ∈ R.subgroupOf T by
        simpa [Subgroup.mem_subgroupOf] using hx)
  have hNamb_le_normR : Namb ≤ Subgroup.normalizer (R : Set G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyN, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hzT : (⟨z, hRT hz⟩ : T) ∈ R.subgroupOf T := by
        simpa [Subgroup.mem_subgroupOf] using hz
      have hconj :=
        (Subgroup.mem_normalizer_iff.mp hyN (⟨z, hRT hz⟩ : T)).1 hzT
      simpa [Subgroup.mem_subgroupOf] using hconj
    · intro hz
      have hyT : (y : G) ∈ T := y.2
      have hconjT : (y : G) * z * (y : G)⁻¹ ∈ T := hRT hz
      have hz_in_T : z ∈ T := by
        have htmp : (y : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * (y : G) ∈ T :=
          T.mul_mem (T.mul_mem (T.inv_mem hyT) hconjT) hyT
        simpa [mul_assoc] using htmp
      have hconj_sub :
          (⟨(y : G) * z * (y : G)⁻¹, hconjT⟩ : T) ∈ R.subgroupOf T := by
        simpa [Subgroup.mem_subgroupOf] using hz
      have hback :=
        (Subgroup.mem_normalizer_iff.mp hyN (⟨z, hz_in_T⟩ : T)).2 hconj_sub
      simpa [Subgroup.mem_subgroupOf] using hback
  have hNamb_le_K : Namb ≤ K := hNamb_le_normR.trans hnormR_le_K
  let NsubK : Subgroup K := Namb.subgroupOf K
  have hNsubK_q : IsPGroup q.val NsubK := by
    have hNamb_q : IsPGroup q.val Namb := by
      have hNsub_q : IsPGroup q.val Nsub := hT_q.to_subgroup Nsub
      simpa [Namb] using IsPGroup.map (p := q.val) (H := Nsub) hNsub_q T.subtype
    exact hNamb_q.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := Namb) (K := K) hNamb_le_K).symm
  have hS_le_NsubK : (S : Subgroup K) ≤ NsubK := by
    intro x hxS
    have hxR : (x : G) ∈ R := by
      have hxAmb : (x : G) ∈ section10AmbientSylowSubgroup K S :=
        Subgroup.mem_map.mpr ⟨x, hxS, rfl⟩
      simpa [hS_eq] using hxAmb
    have hxNamb : (x : G) ∈ Namb := hR_le_Namb hxR
    simpa [NsubK, Subgroup.mem_subgroupOf] using hxNamb
  have hNsubK_eq_S : NsubK = (S : Subgroup K) :=
    S.is_maximal' hNsubK_q hS_le_NsubK
  have hNamb_eq_R : Namb = R := by
    apply le_antisymm
    · intro x hx
      have hxK : x ∈ K := hNamb_le_K hx
      have hxS : (⟨x, hxK⟩ : K) ∈ (S : Subgroup K) := by
        have : (⟨x, hxK⟩ : K) ∈ NsubK := by
          simpa [NsubK, Subgroup.mem_subgroupOf] using hx
        simpa [hNsubK_eq_S] using this
      have hxAmb : x ∈ section10AmbientSylowSubgroup K S :=
        Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, hxS, rfl⟩
      simpa [hS_eq] using hxAmb
    · exact hR_le_Namb
  have hRsub_map : (R.subgroupOf T).map T.subtype = R := by
    simp [inf_eq_left.2 hRT]
  have hNsub_eq_Rsub : Nsub = R.subgroupOf T := by
    apply Subgroup.map_injective T.subtype_injective
    simp [Namb, hNamb_eq_R, hRsub_map]
  exact hRsub_lt_N.ne hNsub_eq_Rsub.symm

public theorem CFSG.section11_ambientSylow_mem_star_of_sigma
    {M A : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hqσ : q ∈ section10SigmaPrimes M)
    (Q : Sylow q.val (section10Msigma M))
    (hAQ :
      A ≤ Subgroup.normalizer
        (section10AmbientSylowSubgroup (section10Msigma M) Q : Set G)) :
    section10AmbientSylowSubgroup (section10Msigma M) Q ∈
      section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
  rcases section11_ambientSylow_isSylow_of_hall
      (theorem_10_2_b hM).1 hqσ (section11_msigma_le M) Q with ⟨S, hS_eq⟩
  refine section11_star_of_ambient_sylow_normalizer_le S hS_eq hAQ ?_
  rw [← hS_eq]
  exact section11_normalizer_ambientSylow_le_of_sigma hM hqσ S

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_conjBy_inv (H : Subgroup G) (g : G) :
    (H.conjBy g).conjBy g⁻¹ = H := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.conjBy, Subgroup.mem_map] at hx
    rcases hx with ⟨y, hy, hyx⟩
    rw [Subgroup.conjBy, Subgroup.mem_map] at hy
    rcases hy with ⟨z, hz, hzy⟩
    have hxz : x = z := by
      rw [← hyx, ← hzy]
      simp [mul_assoc]
    simpa [hxz] using hz
  · intro hx
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · rw [Subgroup.conjBy, Subgroup.mem_map]
      exact ⟨x, hx, by simp [mul_assoc]⟩
    · simp [mul_assoc]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_conjBy_conjBy (H : Subgroup G) (g h : G) :
    (H.conjBy g).conjBy h = H.conjBy (h * g) := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hzy⟩
    exact Subgroup.mem_map.mpr ⟨z, hz, by
      rw [← hyx, ← hzy]
      simp [mul_assoc]⟩
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, hzx⟩
    refine Subgroup.mem_map.mpr ⟨g * z * g⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    · rw [← hzx]
      simp [mul_assoc]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_section7K_le_centralizer (A : Subgroup G) :
    section7K A ≤ Subgroup.centralizer (A : Set G) := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact y.property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_conjBy_inv' (H : Subgroup G) (g : G) :
    (H.conjBy g⁻¹).conjBy g = H := by
  simpa using section11_conjBy_inv (G := G) H g⁻¹


omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_le_conjBy_inv_of_conjBy_le
    {H K : Subgroup G} {g : G} (hHK : H.conjBy g ≤ K) :
    H ≤ K.conjBy g⁻¹ := by
  intro h hh
  rw [Subgroup.conjBy, Subgroup.mem_map]
  refine ⟨g * h * g⁻¹, ?_, ?_⟩
  · exact hHK (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hh)
  · simp [mul_assoc]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_conjBy_eq_of_mem_normalizer
    {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    H.conjBy g = H := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    have hmem : g * y * g⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp hg y).1 hy
    have hxy : x = g * y * g⁻¹ := by
      simpa [MulAut.conj_apply] using hyx.symm
    simpa [hxy] using hmem
  · intro hx
    have hy : g⁻¹ * x * g ∈ H := by
      have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
        Subgroup.inv_mem (Subgroup.normalizer (H : Set G)) hg
      simpa using (Subgroup.mem_normalizer_iff.mp hginv x).1 hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hy, ?_⟩
    simp [MulAut.conj_apply]
    group

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_maximal_conjBy
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) (g : G) :
    M.conjBy g ∈ section9MaximalSubgroups G := by
  have h_map : M.conjBy g = Subgroup.map ((MulAut.conj g : G ≃* G) : G →* G) M := rfl
  rw [h_map]
  exact ((MulAut.conj g : G ≃* G).mapSubgroup.isCoatom_iff M).mpr hM

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_card_conjBy (M : Subgroup G) (g : G) :
    Nat.card (M.conjBy g) = Nat.card M := by
  simpa [Subgroup.conjBy] using
    (Subgroup.card_map_of_injective
      (K := M) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_ambientSylow_conjBy_subgroupOf
    {q : Nat.Primes} (M : Subgroup G) (S : Sylow q.val M) (g : G) :
    let e : M ≃* M.conjBy g := (MulAut.conj g).subgroupMap M
    let R : Subgroup G := (section10AmbientSylowSubgroup M S).conjBy g
    R.subgroupOf (M.conjBy g) = (S : Subgroup M).map e.toMonoidHom := by
  intro e R
  ext x
  constructor
  · intro hx
    change (x : G) ∈ R at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    rw [section10AmbientSylowSubgroup] at hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hzy⟩
    refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
    apply Subtype.ext
    have hzyG : (z : G) = y := hzy
    calc
      ((e z : M.conjBy g) : G) = g * (z : G) * g⁻¹ := by
        rfl
      _ = g * y * g⁻¹ := by rw [hzyG]
      _ = (x : G) := hyx
  · intro hx
    change (x : G) ∈ R
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨z, hz, hzx⟩
    apply Subgroup.mem_map.mpr
    refine ⟨(z : G), ?_, ?_⟩
    · rw [section10AmbientSylowSubgroup, Subgroup.mem_map]
      exact ⟨z, hz, rfl⟩
    · change g * (z : G) * g⁻¹ = (x : G)
      have hzx' := congrArg Subtype.val hzx
      change ((e z : M.conjBy g) : G) = (x : G) at hzx'
      exact hzx'

omit [IsMinCE G] in
public theorem CFSG.section11_ambientSylow_conjBy_exists
    {q : Nat.Primes} (M : Subgroup G) (S : Sylow q.val M) (g : G) :
    ∃ Sg : Sylow q.val (M.conjBy g),
      section10AmbientSylowSubgroup (M.conjBy g) Sg =
        (section10AmbientSylowSubgroup M S).conjBy g := by
  classical
  haveI : Fact q.val.Prime := ⟨q.2⟩
  let e : M ≃* M.conjBy g := (MulAut.conj g).subgroupMap M
  let R : Subgroup (M.conjBy g) := (S : Subgroup M).map e.toMonoidHom
  have hRcard : Nat.card R = q.val ^ (Nat.card (M.conjBy g)).factorization q.val := by
    have hRcardS : Nat.card R = Nat.card (S : Subgroup M) := by
      simpa [R] using
        (Subgroup.card_map_of_injective
          (K := (S : Subgroup M)) (f := e.toMonoidHom) e.injective)
    have hMcard : Nat.card (M.conjBy g) = Nat.card M := section11_card_conjBy M g
    rw [hRcardS, Sylow.card_eq_multiplicity S, hMcard]
  let Sg : Sylow q.val (M.conjBy g) := Sylow.ofCard R hRcard
  refine ⟨Sg, ?_⟩
  have hSg_coe : (Sg : Subgroup (M.conjBy g)) = R := by
    simp [Sg, R]
  have hRsub_eq :
      ((section10AmbientSylowSubgroup M S).conjBy g).subgroupOf (M.conjBy g) = R := by
    simpa [R, e] using section11_ambientSylow_conjBy_subgroupOf (M := M) (S := S) (g := g)
  have hconj_le : (section10AmbientSylowSubgroup M S).conjBy g ≤ M.conjBy g := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
    exact Subgroup.mem_map.mpr ⟨z.1, z.2, rfl⟩
  have hRsub_map :
      (((section10AmbientSylowSubgroup M S).conjBy g).subgroupOf
          (M.conjBy g)).map (M.conjBy g).subtype =
        (section10AmbientSylowSubgroup M S).conjBy g := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hconj_le]
  calc
    section10AmbientSylowSubgroup (M.conjBy g) Sg
        = R.map (M.conjBy g).subtype := by simp [section10AmbientSylowSubgroup, hSg_coe]
    _ = (section10AmbientSylowSubgroup M S).conjBy g := by
      rw [← hRsub_eq]
      exact hRsub_map

omit [IsMinCE G] in
public theorem CFSG.section11_sigma_mem_conjBy
    {M : Subgroup G} {q : Nat.Primes} (hqσ : q ∈ section10SigmaPrimes M) (g : G) :
    q ∈ section10SigmaPrimes (M.conjBy g) := by
  classical
  rcases hqσ with ⟨hqM, S, hnormS_le_M⟩
  rcases section11_ambientSylow_conjBy_exists M S g with ⟨Sg, hSg_eq⟩
  refine ⟨?_, Sg, ?_⟩
  · change q.val ∣ Nat.card (M.conjBy g)
    change q.val ∣ Nat.card M at hqM
    rw [section11_card_conjBy M g]
    exact hqM
  · rw [hSg_eq]
    intro x hx
    have hx_back :
        g⁻¹ * x * g ∈
          Subgroup.normalizer (section10AmbientSylowSubgroup M S : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have hz_g : g * z * g⁻¹ ∈ (section10AmbientSylowSubgroup M S).conjBy g :=
          Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
        have hxz_g : x * (g * z * g⁻¹) * x⁻¹ ∈
            (section10AmbientSylowSubgroup M S).conjBy g :=
          (Subgroup.mem_normalizer_iff.mp hx (g * z * g⁻¹)).1 hz_g
        rcases Subgroup.mem_map.mp hxz_g with ⟨w, hw, hw_eq⟩
        have hw_eq' : w = g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g := by
          rw [← hw_eq]
          simp [mul_assoc]
        have htarget : g⁻¹ * x * g * z * (g⁻¹ * x * g)⁻¹ = w := by
          rw [hw_eq']
          group
        rw [htarget]
        exact hw
      · intro hz
        have hz_g : g * (g⁻¹ * x * g * z * (g⁻¹ * x * g)⁻¹) * g⁻¹ ∈
            (section10AmbientSylowSubgroup M S).conjBy g :=
          Subgroup.mem_map.mpr
            ⟨g⁻¹ * x * g * z * (g⁻¹ * x * g)⁻¹, hz, rfl⟩
        have hpre :
            x * (g * z * g⁻¹) * x⁻¹ ∈
              (section10AmbientSylowSubgroup M S).conjBy g := by
          simpa [mul_assoc] using hz_g
        have hz_g_mem : g * z * g⁻¹ ∈ (section10AmbientSylowSubgroup M S).conjBy g := by
          exact (Subgroup.mem_normalizer_iff.mp hx (g * z * g⁻¹)).2 hpre
        rcases Subgroup.mem_map.mp hz_g_mem with ⟨w, hw, hw_eq⟩
        have hw_eq' : w = z := by
          apply (MulAut.conj g).injective
          simpa [MulAut.conj_apply] using hw_eq
        simpa [hw_eq'] using hw
    have hxM : g⁻¹ * x * g ∈ M := hnormS_le_M hx_back
    exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hxM, by
      simp [MulAut.conj_apply, mul_assoc]⟩

public theorem CFSG.section11_ambientSylow_mem_star_of_sigma_conjBy
    {M A : Subgroup G} {q : Nat.Primes} {g : G}
    (hM : M ∈ section9MaximalSubgroups G) (hqσ : q ∈ section10SigmaPrimes M)
    (Q : Sylow q.val ((section10Msigma M).conjBy g))
    (hAQ :
      A ≤ Subgroup.normalizer
        (section10AmbientSylowSubgroup ((section10Msigma M).conjBy g) Q : Set G)) :
    section10AmbientSylowSubgroup ((section10Msigma M).conjBy g) Q ∈
      section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
  have hHall :
      IsHallSubgroup (section10SigmaPrimes M) ((section10Msigma M).conjBy g) := by
    simpa [Subgroup.conjBy] using (theorem_10_2_b hM).1.map_conj g
  have hMsigma_g_le : (section10Msigma M).conjBy g ≤ M.conjBy g :=
    Subgroup.map_mono (section11_msigma_le M)
  rcases section11_ambientSylow_isSylow_of_hall
      hHall hqσ hMsigma_g_le Q with ⟨S, hS_eq⟩
  refine section11_star_of_ambient_sylow_normalizer_le S hS_eq hAQ ?_
  rw [← hS_eq]
  intro x hx
  have hconj_le :
      (section10AmbientSylowSubgroup (M.conjBy g) S).conjBy x ≤
        M.conjBy g := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
    exact section11_ambientSylow_le (M.conjBy g) S
      ((Subgroup.mem_normalizer_iff.mp hx w).1 hw)
  exact theorem_10_1_d (section11_maximal_conjBy hM g)
    (section11_sigma_mem_conjBy hqσ g) S hconj_le

public theorem CFSG.section11_lemma_7_1_conclusion
    {M A0 A : Subgroup G} {p q : Nat.Primes} {P : Sylow p.val M}
    {g : G}
    (h11 : section11Data M A0 A p P) (hgM : g ∉ M)
    (hqσ : q ∈ section10SigmaPrimes M) (Q1 : Sylow q.val (section10Msigma M))
    (Q2 : Sylow q.val ((section10Msigma M).conjBy g))
    (k : section7K A) (hk : (section10AmbientSylowSubgroup (section10Msigma M) Q1).conjBy (k : G) =
      section10AmbientSylowSubgroup ((section10Msigma M).conjBy g) Q2) : False := by
  rcases section11_ambientSylow_isSylow_of_hall
      (theorem_10_2_b h11.maximal).1 hqσ (section11_msigma_le M) Q1 with
    ⟨S1, hS1_eq⟩
  have hR2_le_Mg : section10AmbientSylowSubgroup ((section10Msigma M).conjBy g) Q2 ≤ M.conjBy g :=
    (section11_ambientSylow_le ((section10Msigma M).conjBy g) Q2).trans
      (Subgroup.map_mono (section11_msigma_le M))
  have hR2_conj_le_M : (section10AmbientSylowSubgroup ((section10Msigma M).conjBy g) Q2).conjBy g⁻¹ ≤ M := by
    have hle : (section10AmbientSylowSubgroup ((section10Msigma M).conjBy g) Q2).conjBy g⁻¹ ≤
        (M.conjBy g).conjBy g⁻¹ :=
      Subgroup.map_mono hR2_le_Mg
    simpa [section11_conjBy_inv M g] using hle
  have hS1_conj_le_M :
      (section10AmbientSylowSubgroup M S1).conjBy (g⁻¹ * (k : G)) ≤ M := by
    calc
      (section10AmbientSylowSubgroup M S1).conjBy (g⁻¹ * (k : G))
          = (section10AmbientSylowSubgroup (section10Msigma M) Q1).conjBy (g⁻¹ * (k : G)) := by
            rw [hS1_eq]
      _ = ((section10AmbientSylowSubgroup (section10Msigma M) Q1).conjBy (k : G)).conjBy g⁻¹ := by
            rw [section11_conjBy_conjBy]
      _ = (section10AmbientSylowSubgroup ((section10Msigma M).conjBy g) Q2).conjBy g⁻¹ := by
            rw [← hk]
      _ ≤ M := hR2_conj_le_M
  have hgkM : g⁻¹ * (k : G) ∈ M :=
    theorem_10_1_d h11.maximal hqσ S1 hS1_conj_le_M
  have hkM : (k : G) ∈ M :=
    h11.centralizer_A_le_M (section11_section7K_le_centralizer A k.property)
  have hg_inv_M : g⁻¹ ∈ M := by
    have hmul : (g⁻¹ * (k : G)) * (k : G)⁻¹ ∈ M :=
      M.mul_mem hgkM (M.inv_mem hkM)
    have hmul_eq : (g⁻¹ * (k : G)) * (k : G)⁻¹ = g⁻¹ := by group
    simpa [hmul_eq] using hmul
  have hgM' : g ∈ M := by
    simpa using M.inv_mem hg_inv_M
  exact hgM hgM'


end Section11

/-!
# Lemma 11.1(a)

This file contains the Section 11 Lemma 11.1(a) statement and proof.
-/

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 11.1(a). -/
public theorem CFSG.lemma_11_1_a
    {M A0 A : Subgroup G} {p q : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {g : G}
    (hgM : g ∉ M) (_hAgM : A ≤ M.conjBy g) (hqσ : q ∈ section10SigmaPrimes M)
    (Q1 : Sylow q.val (section10Msigma M))
    (Q2 : Sylow q.val ((section10Msigma M).conjBy g))
    (hAQ1 :
      A ≤ Subgroup.normalizer
        (section10AmbientSylowSubgroup (section10Msigma M) Q1 : Set G))
    (hAQ2 :
      A ≤ Subgroup.normalizer
        (section10AmbientSylowSubgroup ((section10Msigma M).conjBy g) Q2 : Set G)) :
    section10AmbientSylowSubgroup (section10Msigma M) Q1 ⊓
        section10AmbientSylowSubgroup ((section10Msigma M).conjBy g) Q2 =
      ⊥ := by
  classical
  let R1 : Subgroup G := section10AmbientSylowSubgroup (section10Msigma M) Q1
  let R2 : Subgroup G :=
    section10AmbientSylowSubgroup ((section10Msigma M).conjBy g) Q2
  change R1 ⊓ R2 = ⊥
  by_contra hJ_ne_bot
  have hR1star :
      R1 ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
    simpa [R1] using
      section11_ambientSylow_mem_star_of_sigma h11.maximal hqσ Q1 hAQ1
  have hR2star :
      R2 ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) := by
    simpa [R2] using
      section11_ambientSylow_mem_star_of_sigma_conjBy h11.maximal hqσ Q2 hAQ2
  let J : Subgroup G := R1 ⊓ R2
  let H : Subgroup G := Subgroup.normalizer (J : Set G)
  have hJ_ne_bot' : J ≠ ⊥ := by
    simpa [J] using hJ_ne_bot
  have hA_le_H : A ≤ H := by
    have hA_le_inf :
        A ≤ Subgroup.normalizer (R1 : Set G) ⊓ Subgroup.normalizer (R2 : Set G) := by
      intro a ha
      exact ⟨hR1star.1.2.2 ha, hR2star.1.2.2 ha⟩
    exact hA_le_inf.trans <| by
      simpa [H, J] using
        (Subgroup.inf_normalizer_le_normalizer_inf :
          Subgroup.normalizer (R1 : Set G) ⊓ Subgroup.normalizer (R2 : Set G) ≤
            Subgroup.normalizer ((R1 ⊓ R2 : Subgroup G) : Set G))
  have hJπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) J := by
    exact IsPiSubgroup.of_le (by
      intro x hx
      exact hx.1) hR1star.1.2.1
  have hJ_ne_top : J ≠ ⊤ :=
    section8_ne_top_of_isPiSubgroup_singleton_ne_bot hJπ hJ_ne_bot'
  have hHproper : H ≠ ⊤ :=
    section11_normalizer_ne_top_of_ne_bot_ne_top hJ_ne_bot' hJ_ne_top
  have hHJ_R1_ne_bot : H ⊓ R1 ≠ ⊥ := by
    refine ne_bot_of_le_ne_bot hJ_ne_bot' ?_
    intro x hx
    exact ⟨Subgroup.le_normalizer hx, hx.1⟩
  have hHJ_R2_ne_bot : H ⊓ R2 ≠ ⊥ := by
    refine ne_bot_of_le_ne_bot hJ_ne_bot' ?_
    intro x hx
    exact ⟨Subgroup.le_normalizer hx, hx.2⟩
  obtain ⟨k, hk⟩ :=
    lemma_7_1 (G := G) h11.hypothesis7_1
      (h11.q_not_mem_A_primeSet hqσ) hR1star hR2star
      hA_le_H hHproper hHJ_R1_ne_bot hHJ_R2_ne_bot
  exact section11_lemma_7_1_conclusion h11 hgM hqσ Q1 Q2 k (by simpa [R1, R2] using hk.symm)

end Section11
