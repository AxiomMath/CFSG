module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.corollary_10_7_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_16
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
public theorem CFSG.section10_exists_complementInNormalizer
    {p : Nat.Primes} (P : Sylow p.val G) :
    ∃ V : Subgroup G, section10ComplementInNormalizer P V := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let N : Subgroup G := Subgroup.normalizer (((P : Subgroup G) : Set G))
  let Psub : Subgroup N := (P : Subgroup G).subgroupOf N
  have hHall : IsHallSubgroup ({p} : Set Nat.Primes) Psub := by
    simpa [Psub, N] using section10_sylow_subgroupOf_normalizer_isHall (G := G) P
  obtain ⟨Vsub, hVsub⟩ :=
    Subgroup.exists_right_complement'_of_coprime
      (N := Psub) hHall.card_coprime_index
  refine ⟨Vsub.map N.subtype, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  · have hVsub_eq : ((Vsub.map N.subtype).subgroupOf N) = Vsub := by
      simpa [N] using (subgroupOf_map_subtype_eq (K := N) Vsub)
    change Psub.IsComplement' ((Vsub.map N.subtype).subgroupOf N)
    rw [hVsub_eq]
    exact hVsub

private theorem CFSG.section10_commutatorAction_range_toMulAut_eq
    {R A : Type*} [Group R] [Group A] [MulDistribMulAction A R] :
    let ρ : A →* MulAut R := MulDistribMulAction.toMulAut A R
    commutatorAction (A := ρ.range) (G := R) = commutatorAction (A := A) (G := R) := by
  classical
  let ρ : A →* MulAut R := MulDistribMulAction.toMulAut A R
  dsimp
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨b, r, rfl⟩
    rcases b with ⟨φ, hφ⟩
    rcases hφ with ⟨a, rfl⟩
    refine ⟨a, r, ?_⟩
    simp [MulDistribMulAction.toMulAut_apply]
  · rintro ⟨a, r, rfl⟩
    refine ⟨⟨ρ a, ?_⟩, r, ?_⟩
    · exact ⟨a, rfl⟩
    · simp [ρ, MulDistribMulAction.toMulAut_apply]


omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_omega1_map_subtype_le
    {R : Type*} [Group R] {p : ℕ} (H : Subgroup R) :
    (omega₁ (G := H) (p := p)).map H.subtype ≤ omega₁ (G := R) (p := p) := by
  rw [omega₁, omega, MonoidHom.map_closure]
  refine (Subgroup.closure_le (K := omega₁ (G := R) (p := p))).2 ?_
  rintro _ ⟨x, hx, rfl⟩
  refine Subgroup.subset_closure ?_
  simpa [pow_one] using congrArg H.subtype hx

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_omega1_le_map_subtype_of_forall_pow_eq_one_mem
    {R : Type*} [Group R] {p : ℕ} (H : Subgroup R)
    (hmem : ∀ x : R, x ^ p = 1 → x ∈ H) :
    omega₁ (G := R) (p := p) ≤ (omega₁ (G := H) (p := p)).map H.subtype := by
  rw [omega₁, omega]
  refine (Subgroup.closure_le (K := (omega₁ (G := H) (p := p)).map H.subtype)).2 ?_
  intro x hx
  have hxH : x ∈ H := hmem x (by simpa [pow_one] using hx)
  have hxOmegaH : ⟨x, hxH⟩ ∈ omega₁ (G := H) (p := p) := by
    change ⟨x, hxH⟩ ∈ Subgroup.closure {y : H | y ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    simpa [pow_one] using hx
  exact Subgroup.mem_map_of_mem H.subtype hxOmegaH

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_omega1Z_eq_omega1_of_isCyclic
    {R : Type*} [Group R] [IsCyclic R] {p : ℕ} :
    Ω₁Z p R = omega₁ (G := R) (p := p) := by
  classical
  letI : CommGroup R := IsCyclic.commGroup
  have hcenter : Subgroup.center R = ⊤ := CommGroup.center_eq_top
  apply le_antisymm
  · simpa [Ω₁Z] using
      section10_omega1_map_subtype_le (R := R) (p := p) (Subgroup.center R)
  · have hle :=
      section10_omega1_le_map_subtype_of_forall_pow_eq_one_mem
        (R := R) (p := p) (Subgroup.center R) (fun x _hx => by simp [hcenter])
    simpa [Ω₁Z] using hle

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_omega1_eq_centralProduct_left_of_exponent
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R]
    {R₁ R₂ : Subgroup R}
    (hprod : IsCentralProduct R₁ R₂)
    (hR₁exp : Monoid.exponent R₁ = p)
    (hΩeq :
      (omega₁ (G := R₂) (p := p)).map R₂.subtype = (derivedSubgroup R₁).map R₁.subtype) :
    omega₁ (G := R) (p := p) = R₁ := by
  rcases hprod with ⟨_hR₁norm, _hR₂norm, hcomm12, hsup12⟩
  have hR₁_le_omega : R₁ ≤ omega₁ (G := R) (p := p) := by
    intro y hy
    change y ∈ Subgroup.closure {u : R | u ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    have hy_pow_sub : (⟨y, hy⟩ : R₁) ^ p = 1 := by
      exact
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent (↥R₁) ∣ p by simp [hR₁exp]) ⟨y, hy⟩
    have hy_pow : y ^ p = 1 := by
      simpa using congrArg R₁.subtype hy_pow_sub
    simpa [pow_one] using hy_pow
  have homega_le_R₁ : omega₁ (G := R) (p := p) ≤ R₁ := by
    rw [omega₁, omega]
    refine (Subgroup.closure_le (K := R₁)).2 ?_
    intro x hx
    have hx_pow : x ^ p = 1 := by simpa [pow_one] using hx
    have hx_sup : x ∈ R₁ ⊔ R₂ := by
      rw [hsup12]
      exact Subgroup.mem_top x
    rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := R₁) (t := R₂)).1 hx_sup with
      ⟨y, hy, z, hz, hyz⟩
    let yR₁ : R₁ := ⟨y, hy⟩
    let zR₂ : R₂ := ⟨z, hz⟩
    have hy_cent : (z : R) * (y : R) = (y : R) * (z : R) := by
      exact
        Subgroup.mem_centralizer_iff.mp
          ((Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := R₁) (H₂ := R₂)).1
            hcomm12 hy)
          z hz
    have hy_commute : Commute (y : R) (z : R) := hy_cent.symm
    have hy_pow_sub : yR₁ ^ p = 1 := by
      exact
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent (↥R₁) ∣ p by simp [hR₁exp]) yR₁
    have hy_pow : (y : R) ^ p = 1 := by
      simpa [yR₁] using congrArg R₁.subtype hy_pow_sub
    have hz_pow : (z : R) ^ p = 1 := by
      have hsplit : ((y : R) * (z : R)) ^ p = (y : R) ^ p * (z : R) ^ p := by
        simpa using hy_commute.mul_pow p
      calc
        (z : R) ^ p = (y : R) ^ p * (z : R) ^ p := by simp [hy_pow]
        _ = ((y : R) * (z : R)) ^ p := by simpa using hsplit.symm
        _ = x ^ p := by simp [hyz]
        _ = 1 := hx_pow
    have hz_pow_sub : zR₂ ^ p = 1 := by
      apply Subtype.ext
      simpa [zR₂] using hz_pow
    have hz_omega : zR₂ ∈ omega₁ (G := R₂) (p := p) := by
      change zR₂ ∈ Subgroup.closure {u : R₂ | u ^ (p ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [pow_one] using hz_pow_sub
    have hz_map : (z : R) ∈ (omega₁ (G := R₂) (p := p)).map R₂.subtype :=
      Subgroup.mem_map_of_mem R₂.subtype hz_omega
    rw [hΩeq] at hz_map
    rcases Subgroup.mem_map.mp hz_map with ⟨d, hd, hd_eq⟩
    have hz_R₁ : (z : R) ∈ R₁ := by
      rw [← hd_eq]
      exact d.2
    rw [← hyz]
    exact R₁.mul_mem hy hz_R₁
  exact le_antisymm homega_le_R₁ hR₁_le_omega

private theorem CFSG.section10_complement_commutatorAction_eq_top_ambient
    {p : Nat.Primes} (P : Sylow p.val G) {V : Subgroup G}
    (hVcomp : section10ComplementInNormalizer P V) :
    letI : Subgroup.Normalizes V (P : Subgroup G) := ⟨hVcomp.choose⟩
    commutatorAction (A := V) (G := (P : Subgroup G)) = ⊤ := by
  classical
  rcases hVcomp with ⟨hVleN, hcomp⟩
  letI : Subgroup.Normalizes V (P : Subgroup G) := ⟨hVleN⟩
  have hcomm_ambient : ⁅(P : Subgroup G), V⁆ = (P : Subgroup G) :=
    (corollary_10_7_a (G := G) P ⟨hVleN, hcomp⟩).2
  have hcomm_action_map :
      (commutatorAction (A := V) (G := (P : Subgroup G))).map (P : Subgroup G).subtype =
        ⁅(P : Subgroup G), V⁆ := by
    simpa using
      commutatorAction_subgroup_conj_map_eq_commutator
        (P : Subgroup G) V hVleN
  apply (Subgroup.map_subtype_inj (H := (P : Subgroup G))).mp
  calc
    (commutatorAction (A := V) (G := (P : Subgroup G))).map (P : Subgroup G).subtype =
        ⁅(P : Subgroup G), V⁆ := hcomm_action_map
    _ = (P : Subgroup G) := hcomm_ambient
    _ = (⊤ : Subgroup (P : Subgroup G)).map (P : Subgroup G).subtype := by
      simpa [MonoidHom.range_eq_map] using
        ((P : Subgroup G).range_subtype :
          (P : Subgroup G).subtype.range = (P : Subgroup G)).symm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_subgroupOf_conjBy_map_subtype
    {M H : Subgroup G} (hHM : H ≤ M) (m : M) :
    ((H.subgroupOf M).conjBy m).map M.subtype = H.conjBy (m : G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y ∈ (H.subgroupOf M).map (MulAut.conj m).toMonoidHom at hy
    rw [Subgroup.mem_map] at hy
    change ((y : M) : G) ∈ H.map (MulAut.conj (m : G)).toMonoidHom
    rw [Subgroup.mem_map]
    rcases hy with ⟨z, hz, hzy⟩
    refine ⟨(z : G), ?_, ?_⟩
    · exact hz
    · exact congrArg Subtype.val hzy
  · intro hx
    change x ∈ H.map (MulAut.conj (m : G)).toMonoidHom at hx
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨z, hz, hzx⟩
    let zM : M := ⟨z, hHM hz⟩
    refine ⟨m * zM * m⁻¹, ?_, ?_⟩
    · change m * zM * m⁻¹ ∈ (H.subgroupOf M).map (MulAut.conj m).toMonoidHom
      rw [Subgroup.mem_map]
      refine ⟨zM, ?_, ?_⟩
      · exact hz
      · ext
        simp [MulAut.conj_apply, zM, mul_assoc]
    · change (m : G) * z * (m : G)⁻¹ = x
      simpa [MulAut.conj_apply, mul_assoc] using hzx


omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_nilpotencyClassLe_of_card_le_p_cubed
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (hcard : Nat.card R ≤ p ^ 3) :
    NilpotencyClassLe 2 R := by
  let hp : Nat.Prime p := Fact.out
  let hRp : IsPGroup p R := Fact.out
  rcases subsingleton_or_nontrivial R with hsub | hnontriv
  · letI : Subsingleton R := hsub
    haveI : Group.IsNilpotent R := Group.isNilpotent_of_subsingleton
    have hnil : Group.nilpotencyClass R = 0 :=
      (Group.nilpotencyClass_zero_iff_subsingleton (G := R)).2 hsub
    exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le
      (G := R) (n := 2)).2 <| by
      simp [hnil]
  letI : Nontrivial R := hnontriv
  letI : Group.IsNilpotent R := hRp.isNilpotent
  have hquot_p : IsPGroup p (R ⧸ Subgroup.center R) := hRp.to_quotient (Subgroup.center R)
  have hcenter_ne_bot : Subgroup.center R ≠ ⊥ := by
    exact ne_of_gt hRp.bot_lt_center
  obtain ⟨n, hn_pos, hcardR_eq⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := R) hRp).mp hnontriv
  have hcenter_card_ge : p ≤ Nat.card (Subgroup.center R) := by
    obtain ⟨k, hk, hcard_center⟩ :=
      IsPGroup.card_center_eq_prime_pow (G := R) (p := p) hcardR_eq hn_pos
    have hk_pos : 1 ≤ k := by
      have hcard_center_pos : 1 < Nat.card (Subgroup.center R) := by
        exact (Subgroup.one_lt_card_iff_ne_bot (H := Subgroup.center R)).2 hcenter_ne_bot
      rw [hcard_center] at hcard_center_pos
      cases k with
      | zero =>
          simp at hcard_center hcard_center_pos
      | succ k =>
          exact Nat.succ_le_succ (Nat.zero_le _)
    calc
      p = p ^ 1 := by simp
      _ ≤ p ^ k := (Nat.pow_le_pow_iff_right hp.one_lt).2 hk_pos
      _ = Nat.card (Subgroup.center R) := hcard_center.symm
  have hquot_card_le : Nat.card (R ⧸ Subgroup.center R) ≤ p ^ 2 := by
    have hmul :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup
        (α := R) (s := Subgroup.center R)
    have hdiv : Nat.card (R ⧸ Subgroup.center R) * p ≤ Nat.card R := by
      calc
        Nat.card (R ⧸ Subgroup.center R) * p
            ≤ Nat.card (R ⧸ Subgroup.center R) * Nat.card (Subgroup.center R) :=
              Nat.mul_le_mul_left _ hcenter_card_ge
        _ = Nat.card R := by simpa [Nat.mul_comm] using hmul.symm
    have hpow : Nat.card (R ⧸ Subgroup.center R) * p ≤ p ^ 3 := le_trans hdiv hcard
    have hcancel := Nat.le_of_mul_le_mul_right hpow hp.pos
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcancel
  have hquot_comm : IsMulCommutative (R ⧸ Subgroup.center R) := by
    have hcard_quot_eq :
        Nat.card (R ⧸ Subgroup.center R) = p ^ 2 ∨
          Nat.card (R ⧸ Subgroup.center R) = p ^ 1 ∨
          Nat.card (R ⧸ Subgroup.center R) = p ^ 0 := by
      obtain ⟨n, hn⟩ := hquot_p.exists_card_eq
      have hn_le_two : n ≤ 2 := by
        have : p ^ n ≤ p ^ 2 := by simpa [hn] using hquot_card_le
        exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
      interval_cases n <;> simp [hn]
    rcases hcard_quot_eq with h2 | h1 | h0
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq
        (p := p) (G := R ⧸ Subgroup.center R) h2
    · have hcyc : IsCyclic (R ⧸ Subgroup.center R) :=
        isCyclic_of_prime_card (α := R ⧸ Subgroup.center R) (by simpa using h1)
      exact hcyc.isMulCommutative
    · have hsub : Subsingleton (R ⧸ Subgroup.center R) :=
        (Nat.card_eq_one_iff_unique.mp (by simpa using h0)).1
      letI : Subsingleton (R ⧸ Subgroup.center R) := hsub
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  have hnil_cls : Group.nilpotencyClass R ≤ 2 := by
    letI : IsMulCommutative (R ⧸ Subgroup.center R) := hquot_comm
    letI : CommGroup (R ⧸ Subgroup.center R) := IsMulCommutative.instCommGroup
    have hquot_nil : Group.nilpotencyClass (R ⧸ Subgroup.center R) ≤ 1 := by
      simpa using (CommGroup.nilpotencyClass_le_one (G := R ⧸ Subgroup.center R))
    have hker_center : (QuotientGroup.mk' (Subgroup.center R) :
        R →* R ⧸ Subgroup.center R).ker ≤ Subgroup.center R := by
      simp [QuotientGroup.ker_mk']
    have hbound :=
      Group.nilpotencyClass_le_of_ker_le_center
        (QuotientGroup.mk' (Subgroup.center R)) hker_center
    calc
      Group.nilpotencyClass R ≤ Group.nilpotencyClass (R ⧸ Subgroup.center R) + 1 := hbound
      _ ≤ 1 + 1 := Nat.add_le_add_right hquot_nil 1
      _ = 2 := by norm_num
  exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le
    (G := R) (n := 2)).2 hnil_cls

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_natCard_lt_of_subgroup_lt
    {R : Type*} [Group R] [Finite R] {H K : Subgroup R} (hHK : H < K) :
    Nat.card H < Nat.card K := by
  let HK : Subgroup K := H.subgroupOf K
  have hHK_card : Nat.card HK = Nat.card H := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := H) (K := K) hHK.1).toEquiv
  have hHK_ne_top : HK ≠ ⊤ := by
    intro htop
    apply hHK.2
    intro x hx
    have hx_top : (⟨x, hx⟩ : K) ∈ (⊤ : Subgroup K) := by simp
    have hx_HK : (⟨x, hx⟩ : K) ∈ HK := by simp [htop]
    simpa [HK, Subgroup.mem_subgroupOf] using hx_HK
  have hle : Nat.card HK ≤ Nat.card K := Subgroup.card_le_card_group (H := HK)
  have hne : Nat.card HK ≠ Nat.card K := by
    intro hEq
    exact hHK_ne_top ((Subgroup.card_eq_iff_eq_top (H := HK)).1 hEq)
  have hlt : Nat.card HK < Nat.card K := lt_of_le_of_ne hle hne
  simpa [hHK_card] using hlt

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_isExtraspecial_of_noncommutative_card_p3_exponent_p
    {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p K)]
    (hKcard : Nat.card K = p ^ 3) (hKexp : Monoid.exponent K = p)
    (hKnoncomm : ¬ IsMulCommutative K) :
    IsExtraspecial p K := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hKnontriv : Nontrivial K := by
    have hcard_gt : 1 < Nat.card K := by
      rw [hKcard]
      exact one_lt_pow₀ hp.one_lt (by decide)
    exact Finite.one_lt_card_iff_nontrivial.mp hcard_gt
  letI : Nontrivial K := hKnontriv
  have hclass2 : NilpotencyClassLe 2 K :=
    section10_nilpotencyClassLe_of_card_le_p_cubed (R := K) (p := p) (by rw [hKcard])
  have hcomm_center : commutator K ≤ Subgroup.center K :=
    commutator_le_center_of_le_upperCentralSeries_two (G := K) (⊤ : Subgroup K)
      (by simpa [hclass2])
  have hcenter_ne_top : Subgroup.center K ≠ ⊤ := by
    intro htop
    apply hKnoncomm
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxcent : x ∈ Subgroup.center K := by simp [htop]
    exact (Subgroup.mem_center_iff.mp hxcent y).symm
  have hcenter_lt_top : Subgroup.center K < (⊤ : Subgroup K) :=
    lt_of_le_of_ne le_top hcenter_ne_top
  have hcenter_card_lt : Nat.card (Subgroup.center K) < p ^ 3 := by
    have hlt := section10_natCard_lt_of_subgroup_lt (R := K)
      (H := Subgroup.center K) (K := (⊤ : Subgroup K)) hcenter_lt_top
    simpa [hKcard] using hlt
  have hcenter_p : IsPGroup p (Subgroup.center K) :=
    (Fact.out : IsPGroup p K).to_subgroup (Subgroup.center K)
  obtain ⟨m, hm⟩ := hcenter_p.exists_card_eq
  have hm_pos : 0 < m := by
    have hcenter_nontriv : Nontrivial (Subgroup.center K) :=
      IsPGroup.center_nontrivial (p := p) (G := K) (hG := Fact.out)
    have hcard_gt_one : 1 < Nat.card (Subgroup.center K) :=
      Finite.one_lt_card_iff_nontrivial.mpr hcenter_nontriv
    rw [hm] at hcard_gt_one
    by_contra hm_zero
    have : m = 0 := by omega
    simp [this] at hcard_gt_one
  have hm_lt_three : m < 3 := by
    rw [hm] at hcenter_card_lt
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 hcenter_card_lt
  have hm_le_two : m ≤ 2 := by omega
  have hm_eq_one : m = 1 := by
    by_contra hm_ne_one
    have hm_eq_two : m = 2 := by omega
    have hcenter_card_sq : Nat.card (Subgroup.center K) = p ^ 2 := by
      simpa [hm_eq_two] using hm
    have hquot_card : Nat.card (K ⧸ Subgroup.center K) = p := by
      have hmul :
          Nat.card (K ⧸ Subgroup.center K) * p ^ 2 = p * p ^ 2 := by
        calc
          Nat.card (K ⧸ Subgroup.center K) * p ^ 2
              = Nat.card (K ⧸ Subgroup.center K) * Nat.card (Subgroup.center K) := by
                  rw [hcenter_card_sq]
          _ = Nat.card K := by
                simpa using
                  (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := K)
                    (s := Subgroup.center K)).symm
          _ = p ^ 3 := hKcard
          _ = p * p ^ 2 := by ring_nf
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) hmul
    have hquot_cyc : IsCyclic (K ⧸ Subgroup.center K) :=
      isCyclic_of_prime_card (α := K ⧸ Subgroup.center K) hquot_card
    letI : IsCyclic (K ⧸ Subgroup.center K) := hquot_cyc
    apply hKnoncomm
    exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center K))
      (by simp [QuotientGroup.ker_mk'])
  have hcenter_card : Nat.card (Subgroup.center K) = p := by
    simpa [hm_eq_one] using hm
  have hquot_nontriv : Nontrivial (K ⧸ Subgroup.center K) := by
    by_contra htriv
    haveI : Subsingleton (K ⧸ Subgroup.center K) := not_nontrivial_iff_subsingleton.mp htriv
    have hcenter_top : Subgroup.center K = ⊤ :=
      QuotientGroup.subgroup_eq_top_of_subsingleton (Subgroup.center K) inferInstance
    apply hKnoncomm
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxcent : x ∈ Subgroup.center K := by simp [hcenter_top]
    exact (Subgroup.mem_center_iff.mp hxcent y).symm
  letI : Nontrivial (K ⧸ Subgroup.center K) := hquot_nontriv
  exact {
    center_order_p := hcenter_card
    quotient_elementary_abelian :=
      isElementaryAbelian_quotient_center_of_commutator_le_center_of_exponent_eq
        hcomm_center hKexp
    quotient_nontrivial := hquot_nontriv
  }

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_derivedSubgroup_map_subtype_eq_center_map_subtype_of_isExtraspecial
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (S : Subgroup R) [IsExtraspecial p S] :
    (derivedSubgroup S).map S.subtype = (Subgroup.center S).map S.subtype := by
  classical
  let ZS : Subgroup R := (Subgroup.center S).map S.subtype
  have hder_le_ZS : (derivedSubgroup S).map S.subtype ≤ ZS := by
    exact Subgroup.map_mono (commutator_le_center_of_isExtraspecial_local (q := p) (K := S))
  have hcenter_le_der : Subgroup.center S ≤ derivedSubgroup S := by
    have hder_ne_bot : derivedSubgroup S ≠ ⊥ := by
      intro hder_bot
      have hcomm_le_bot : commutator S ≤ (⊥ : Subgroup S) := by
        change derivedSeries S 1 = ⊥ at hder_bot
        rw [derivedSeries_one] at hder_bot
        exact le_of_eq hder_bot
      have hcommS : IsMulCommutative S := by
        refine ⟨⟨?_⟩⟩
        intro x y
        have hxy_mem : ⁅x, y⁆ ∈ (commutator S) :=
          Subgroup.commutator_mem_commutator
            (H₁ := (⊤ : Subgroup S)) (H₂ := (⊤ : Subgroup S)) (by simp) (by simp)
        have hxy_bot : ⁅x, y⁆ ∈ (⊥ : Subgroup S) := hcomm_le_bot hxy_mem
        have hxy_one : ⁅x, y⁆ = 1 := by simpa using hxy_bot
        exact commutatorElement_eq_one_iff_mul_comm.mp hxy_one
      have hcenter_top : Subgroup.center S = ⊤ := by
        ext x
        constructor
        · intro _; simp
        · intro _
          rw [Subgroup.mem_center_iff]
          intro y
          exact (hcommS.is_comm.comm x y).symm
      have hquot_subsingleton : Subsingleton (S ⧸ Subgroup.center S) := by
        exact (QuotientGroup.subsingleton_iff (N := Subgroup.center S)).2 hcenter_top
      exact not_nontrivial_iff_subsingleton.mpr hquot_subsingleton
        (IsExtraspecial.quotient_nontrivial p S)
    exact center_le_of_le_center_ne_bot_of_prime_center_local
      (K := S) (q := p) (hcenter := IsExtraspecial.center_order_p p S)
      (commutator_le_center_of_isExtraspecial_local (q := p) (K := S))
      hder_ne_bot
  have hZS_le_der : ZS ≤ (derivedSubgroup S).map S.subtype := by
    exact Subgroup.map_mono hcenter_le_der
  exact le_antisymm hder_le_ZS hZS_le_der

omit [IsMinCE G] in
public theorem CFSG.section10_omegaOneCenter_eq_center_map_of_centralProduct
    {P : Subgroup G} {Q Y : Subgroup P} {p : Nat.Primes}
    (hQcard : Nat.card Q = p.val ^ 3)
    (hQnoncomm : ¬ IsMulCommutative Q)
    (hQexp : Monoid.exponent Q = p.val)
    (hYcyc : IsCyclic Y)
    (hcentral : IsCentralProduct Q Y)
    (hΩeq :
      (Ω₁Z p.val Y).map Y.subtype = (Subgroup.center Q).map Q.subtype) :
    section10OmegaOneCenter p P =
      ((Subgroup.center Q).map Q.subtype).map P.subtype := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hQp : IsPGroup p.val Q := IsPGroup.of_card (n := 3) hQcard
  letI : Fact (IsPGroup p.val Q) := ⟨hQp⟩
  have hQextra : IsExtraspecial p.val Q :=
      section10_isExtraspecial_of_noncommutative_card_p3_exponent_p
      (K := Q) (p := p.val) hQcard hQexp hQnoncomm
  letI : IsExtraspecial p.val Q := hQextra
  have hder_center :
      (derivedSubgroup Q).map Q.subtype =
        (Subgroup.center Q).map Q.subtype :=
    section10_derivedSubgroup_map_subtype_eq_center_map_subtype_of_isExtraspecial
      (R := P) (p := p.val) Q
  have hΩder :
      (omega₁ (G := Y) (p := p.val)).map Y.subtype =
        (derivedSubgroup Q).map Q.subtype := by
    letI : IsCyclic Y := hYcyc
    calc
      (omega₁ (G := Y) (p := p.val)).map Y.subtype =
          (Ω₁Z p.val Y).map Y.subtype := by
            rw [← section10_omega1Z_eq_omega1_of_isCyclic (R := Y) (p := p.val)]
      _ = (Subgroup.center Q).map Q.subtype := hΩeq
      _ = (derivedSubgroup Q).map Q.subtype := hder_center.symm
  have homegaP : omega₁ (G := P) (p := p.val) = Q :=
    section10_omega1_eq_centralProduct_left_of_exponent
      (p := p.val) (R := P) (R₁ := Q) (R₂ := Y) hcentral hQexp hΩder
  apply le_antisymm
  · intro z hz
    change z ∈ (Ω₁Z p.val P).map P.subtype at hz
    rcases Subgroup.mem_map.mp hz with ⟨zP, hzΩ, rfl⟩
    have hzωP : zP ∈ omega₁ (G := P) (p := p.val) := by
      simpa [Ω₁Z] using
        section10_omega1_map_subtype_le
          (R := P) (p := p.val) (Subgroup.center P) hzΩ
    have hzQ : zP ∈ Q := by
      simpa [homegaP] using hzωP
    have hzcenterP : zP ∈ Subgroup.center P := by
      rcases Subgroup.mem_map.mp hzΩ with ⟨zc, _hzcΩ, hzc_eq⟩
      rw [← hzc_eq]
      exact (zc : Subgroup.center P).property
    have hzcenterQ : (⟨zP, hzQ⟩ : Q) ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hzcenterP (y : P)
    exact Subgroup.mem_map.mpr
      ⟨zP, Subgroup.mem_map.mpr ⟨⟨zP, hzQ⟩, hzcenterQ, rfl⟩, rfl⟩
  · intro z hz
    change z ∈ ((Subgroup.center Q).map Q.subtype).map P.subtype at hz
    rcases Subgroup.mem_map.mp hz with ⟨zP, hzP, rfl⟩
    rcases Subgroup.mem_map.mp hzP with ⟨zQ, hzQcenter, hzQ_eq⟩
    rcases hcentral with ⟨_hQnorm, _hYnorm, hcommQY, hsupQY⟩
    have hzP_center : zP ∈ Subgroup.center P := by
      rw [← hzQ_eq]
      rw [Subgroup.mem_center_iff]
      intro w
      have hw_sup : w ∈ Q ⊔ Y := by
        rw [hsupQY]
        exact Subgroup.mem_top w
      rcases (Subgroup.mem_sup_of_normal_left (x := w) (s := Q) (t := Y)).1 hw_sup with
        ⟨q, hq, y, hy, hqy⟩
      have hzq_comm : (zQ : P) * q = q * (zQ : P) := by
        have hzq :=
          congrArg (fun u : Q => (u : P))
            (Subgroup.mem_center_iff.mp hzQcenter ⟨q, hq⟩)
        simpa using hzq.symm
      have hzy_comm : (zQ : P) * y = y * (zQ : P) := by
        have hQ_le_centY : Q ≤ Subgroup.centralizer (Y : Set P) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Q) (H₂ := Y)).1 hcommQY
        exact (Subgroup.mem_centralizer_iff.mp (hQ_le_centY zQ.property) y hy).symm
      calc
        w * (zQ : P) = (q * y) * (zQ : P) := by rw [hqy]
        _ = q * (y * (zQ : P)) := by simp [mul_assoc]
        _ = q * ((zQ : P) * y) := by rw [← hzy_comm]
        _ = (q * (zQ : P)) * y := by simp [mul_assoc]
        _ = ((zQ : P) * q) * y := by rw [← hzq_comm]
        _ = (zQ : P) * (q * y) := by simp [mul_assoc]
        _ = (zQ : P) * w := by rw [hqy]
    have hzP_pow : zP ^ p.val = 1 := by
      rw [← hzQ_eq]
      have hzQ_pow : zQ ^ p.val = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent Q ∣ p.val by rw [hQexp]) zQ
      have hzQ_powP := congrArg (fun u : Q => (u : P)) hzQ_pow
      exact hzQ_powP
    have hzΩ : zP ∈ Ω₁Z p.val P := by
      change zP ∈
        (omega₁ (G := Subgroup.center P) (p := p.val)).map
          (Subgroup.center P).subtype
      let zC : Subgroup.center P := ⟨zP, hzP_center⟩
      have hzCΩ : zC ∈ omega₁ (G := Subgroup.center P) (p := p.val) := by
        change zC ∈ Subgroup.closure {y : Subgroup.center P | y ^ (p.val ^ 1) = 1}
        refine Subgroup.subset_closure ?_
        apply Subtype.ext
        simpa [pow_one, zC] using hzP_pow
      exact Subgroup.mem_map_of_mem (Subgroup.center P).subtype hzCΩ
    exact Subgroup.mem_map.mpr ⟨zP, hzΩ, rfl⟩

/-- Corollary 10.7(b). -/
public theorem CFSG.corollary_10_7_b
    {p : Nat.Primes} (P : Sylow p.val G)
    (hPrank : groupRank (P : Subgroup G) ≤ 2) :
    IsMulCommutative (P : Subgroup G) ∨
      section10SpecialRankTwoSylowShape (H := P) p := by
  classical
  by_cases hPbot : (P : Subgroup G) = ⊥
  · left
    haveI : Subsingleton (P : Subgroup G) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hPbot] using x.property
      have hybot : (y : G) ∈ (⊥ : Subgroup G) := by
        simpa [hPbot] using y.property
      have hxone : (x : G) = 1 := by simpa using hxbot
      have hyone : (y : G) = 1 := by simpa using hybot
      simp [hxone, hyone]
    exact ⟨⟨fun x y => Subsingleton.elim (x * y) (y * x)⟩⟩
  · haveI : Fact p.val.Prime := ⟨p.property⟩
    haveI : Nontrivial (P : Subgroup G) :=
      (Subgroup.nontrivial_iff_ne_bot (P : Subgroup G)).2 hPbot
    haveI : Fact (IsPGroup p.val (P : Subgroup G)) := ⟨P.isPGroup'⟩
    have hp_dvd_P : p.val ∣ Nat.card (P : Subgroup G) := by
      rcases P.isPGroup'.card_eq_or_dvd with hcard | hdiv
      · exact False.elim (hPbot ((Subgroup.card_eq_one (H := (P : Subgroup G))).mp hcard))
      · exact hdiv
    have hp_dvd_G : p.val ∣ Nat.card G :=
      hp_dvd_P.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup G))
    have hpodd : p.val ≠ 2 :=
      Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
    obtain ⟨V, hVcomp⟩ := section10_exists_complementInNormalizer (G := G) P
    rcases hVcomp with ⟨hVleN, hcomp⟩
    letI : Subgroup.Normalizes V (P : Subgroup G) := ⟨hVleN⟩
    let ρ : V →* MulAut (P : Subgroup G) :=
      MulDistribMulAction.toMulAut V (P : Subgroup G)
    have hcommV :
        commutatorAction (A := V) (G := (P : Subgroup G)) = ⊤ := by
      simpa using
        section10_complement_commutatorAction_eq_top_ambient
          (G := G) P (V := V) ⟨hVleN, hcomp⟩
    have hcommρ :
        commutatorAction (A := ρ.range) (G := (P : Subgroup G)) = ⊤ := by
      have h :=
        section10_commutatorAction_range_toMulAut_eq
          (R := (P : Subgroup G)) (A := V)
      exact (by simpa [ρ] using h.trans hcommV)
    let N : Subgroup G := Subgroup.normalizer (((P : Subgroup G) : Set G))
    let Psub : Subgroup N := (P : Subgroup G).subgroupOf N
    let Vsub : Subgroup N := V.subgroupOf N
    have hHall : IsHallSubgroup ({p} : Set Nat.Primes) Psub := by
      simpa [Psub, N] using section10_sylow_subgroupOf_normalizer_isHall (G := G) P
    have hp_not_Psub_index : ¬ p.val ∣ Psub.index := by
      intro hpidx
      exact (hHall.p_in_pi_of_p_dvd_index p hpidx) (by simp)
    have hcop_index : Nat.Coprime p.val Psub.index :=
      (p.property.coprime_iff_not_dvd).2 hp_not_Psub_index
    have hPsub_index_card_Vsub : Psub.index = Nat.card Vsub := by
      simpa [Psub, Vsub, N] using hcomp.symm.index_eq_card
    have hcard_Vsub_V : Nat.card Vsub = Nat.card V := by
      simpa [Vsub, N] using
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := V) (K := N) hVleN).toEquiv
    have hcopV : Nat.Coprime p.val (Nat.card V) := by
      simpa [hPsub_index_card_Vsub, hcard_Vsub_V] using hcop_index
    have hcopρ : Nat.Coprime p.val (Nat.card ρ.range) :=
      Nat.Coprime.of_dvd_right (Subgroup.card_range_dvd ρ) hcopV
    have hVodd : Odd (Nat.card V) :=
      odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card V)
    have hρodd : Odd (Nat.card ρ.range) :=
      odd_of_card_dvd hVodd (Subgroup.card_range_dvd ρ)
    haveI : FaithfulSMul ρ.range (P : Subgroup G) := inferInstance
    rcases
      (theorem_4_16 (R := (P : Subgroup G)) (A := ρ.range) (p := p.val)
        hpodd hcopρ hPrank hcommρ hρodd).2 with hcommP | hshape
    · exact Or.inl hcommP
    · rcases hshape with
        ⟨P₁, P₂, hcentral, hP₁card, hP₁exp, hP₁noncomm, hP₂cyc, hΩder⟩
      have hP₁p : IsPGroup p.val P₁ :=
        (Fact.out : IsPGroup p.val (P : Subgroup G)).to_subgroup P₁
      letI : Fact (IsPGroup p.val P₁) := ⟨hP₁p⟩
      have hP₁extra : IsExtraspecial p.val P₁ :=
        section10_isExtraspecial_of_noncommutative_card_p3_exponent_p
          (K := P₁) (p := p.val) hP₁card hP₁exp hP₁noncomm
      letI : IsExtraspecial p.val P₁ := hP₁extra
      have hder_center :
          (derivedSubgroup P₁).map P₁.subtype =
            (Subgroup.center P₁).map P₁.subtype :=
        section10_derivedSubgroup_map_subtype_eq_center_map_subtype_of_isExtraspecial
          (R := (P : Subgroup G)) (p := p.val) P₁
      have hΩcenter :
          (Ω₁Z p.val P₂).map P₂.subtype =
            (Subgroup.center P₁).map P₁.subtype := by
        letI : IsCyclic P₂ := hP₂cyc
        calc
          (Ω₁Z p.val P₂).map P₂.subtype =
              (omega₁ (G := P₂) (p := p.val)).map P₂.subtype := by
            rw [section10_omega1Z_eq_omega1_of_isCyclic (R := P₂) (p := p.val)]
          _ = (derivedSubgroup P₁).map P₁.subtype := hΩder
          _ = (Subgroup.center P₁).map P₁.subtype := hder_center
      exact Or.inr ⟨P₁, P₂, hP₁card, hP₁noncomm, hP₁exp, hP₂cyc, hcentral, hΩcenter⟩
