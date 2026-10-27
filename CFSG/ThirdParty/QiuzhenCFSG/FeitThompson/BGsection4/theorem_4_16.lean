module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

import Mathlib.GroupTheory.Schreier
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_8_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_8_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_10
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_11
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_12_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_12_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_13
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_15
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.gorenstein_5_4_15

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 4.16 from BG Section 4 -/

universe u

section Main

open scoped FixedPoints commutatorElement

private theorem CFSG.generatorRank_at_least_three_of_elementaryAbelian_card_p3_local
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 3) :
    3 ≤ generatorRank A := by
  letI : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  rw [hA] at hcard_dvd
  have hle_rank : 3 ≤ Group.rank A := by
    exact (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_dvd
  simpa [generatorRank_eq_group_rank] using hle_rank


private theorem CFSG.commutatorAction_eq_bot_of_actsTrivially_local
    {R A : Type*} [Group R] [Group A] [MulDistribMulAction A R]
    (htriv : ActsTrivially (A := A) (G := R)) :
    commutatorAction (A := A) (G := R) = ⊥ := by
  rw [commutatorAction_eq_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨a, r, rfl⟩
    have hfix : a • r = r := htriv a r
    simp [hfix]
  · exact bot_le

private theorem CFSG.subgroup_top_ne_bot_of_nontrivial
    {R : Type*} [Group R] [Nontrivial R] :
    (⊤ : Subgroup R) ≠ ⊥ := by
  intro htop_bot
  have hsub : Subsingleton R := by
    constructor
    intro x y
    have hx : x ∈ (⊥ : Subgroup R) := by
      rw [← htop_bot]
      simp
    have hy : y ∈ (⊥ : Subgroup R) := by
      rw [← htop_bot]
      simp
    have hx_one : x = 1 := by simpa using hx
    have hy_one : y = 1 := by simpa using hy
    rw [hx_one, hy_one]
  exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance

private theorem CFSG.not_actsTrivially_of_commutatorAction_eq_top
    {R A : Type*} [Group R] [Nontrivial R] [Group A] [MulDistribMulAction A R]
    (hcomm : commutatorAction (A := A) (G := R) = ⊤) :
    ¬ ActsTrivially (A := A) (G := R) := by
  intro htriv
  have hbot : commutatorAction (A := A) (G := R) = ⊥ :=
    commutatorAction_eq_bot_of_actsTrivially_local htriv
  exact subgroup_top_ne_bot_of_nontrivial (R := R) (hcomm ▸ hbot)

private theorem CFSG.theorem_4_16_prime_gt_three
    {R A : Type*} [Group R] [Finite R] [Nontrivial R] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p R)]
    [MulDistribMulAction A R] [FaithfulSMul A R] (hcop : Nat.Coprime p (Nat.card A))
    (hrank : groupRank R ≤ 2) (hcomm : commutatorAction (A := A) (G := R) = ⊤)
    (hAodd : Odd (Nat.card A)) :
    3 < p := by
  classical
  have hA3 : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅ :=
    selfCentralizingAbelianSubgroupsAtLeast_eq_empty_of_groupRank_le_two
      (R := R) (p := p) (Fact.out : IsPGroup p R) hrank
  have hntriv : ¬ ActsTrivially (A := A) (G := R) :=
    not_actsTrivially_of_commutatorAction_eq_top (R := R) (A := A) hcomm
  have hAcard_ne_one : Nat.card A ≠ 1 := by
    intro hAcard
    have hsub : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hAcard).1
    letI : Subsingleton A := hsub
    apply hntriv
    intro a r
    have ha : a = 1 := Subsingleton.elim a 1
    simp [ha]
  obtain ⟨q, hqprime, hqdvdA⟩ := Nat.exists_prime_and_dvd hAcard_ne_one
  haveI : Fact q.Prime := ⟨hqprime⟩
  have hq_ne_two : q ≠ 2 := by
    intro hq
    have htwo_dvd : 2 ∣ Nat.card A := by simpa [hq] using hqdvdA
    have hnot_two_dvd : ¬ 2 ∣ Nat.card A := by
      have hnot_even : ¬ Even (Nat.card A) := by
        rw [Nat.not_even_iff_odd]
        exact hAodd
      simpa [even_iff_two_dvd] using hnot_even
    exact hnot_two_dvd htwo_dvd
  have hq_ne_p : q ≠ p := by
    intro hq_eq
    have hp_not_dvd_A : ¬ p ∣ Nat.card A :=
      (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hcop
    exact hp_not_dvd_A (by simpa [hq_eq] using hqdvdA)
  have hqAut : q ∣ Nat.card (MulAut R) := by
    let φ : A →* MulAut R := MulDistribMulAction.toMulAut A R
    have hφinj : Function.Injective φ := by
      intro a b hab
      apply FaithfulSMul.eq_of_smul_eq_smul (α := R)
      intro r
      have hr := congrArg (fun f : MulAut R => f r) hab
      simpa [φ, MulDistribMulAction.toMulAut_apply] using hr
    exact hqdvdA.trans (Subgroup.card_dvd_of_injective φ hφinj)
  obtain ⟨_hq_dvd, hq_lt_p⟩ :=
    lemma_4_13 (R := R) (p := p) (q := q) hpodd hA3 hqAut hq_ne_p
  have hq_ge_three : 3 ≤ q := by
    have hq_two_le : 2 ≤ q := hqprime.two_le
    omega
  omega

private theorem CFSG.theorem_4_16_small_omega_commutative
    {R A : Type*} [Group R] [Finite R] [Nontrivial R] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p R)]
    [MulDistribMulAction A R] (hcop : Nat.Coprime p (Nat.card A))
    (hcomm : commutatorAction (A := A) (G := R) = ⊤)
    (hpgt : 3 < p)
    (hOmega : Nat.card (omega₁ (G := R) (p := p)) ≤ p ^ 2) :
    IsMulCommutative R := by
  classical
  have hmeta : IsMetacyclic R :=
    proposition_4_11 (R := R) (p := p) hpgt hOmega
  by_contra hncomm
  have hntriv : ¬ ActsTrivially (A := A) (G := R) :=
    not_actsTrivially_of_commutatorAction_eq_top (R := R) (A := A) hcomm
  obtain ⟨_hT_ne, hTcyc, _hC_ne, _hCcyc, _hder_le⟩ :=
    theorem_4_12_c (R := R) (A := A) (p := p) hpodd hcop hmeta hncomm hntriv
  have htop_cyc : IsCyclic (⊤ : Subgroup R) := by
    exact (MulEquiv.subgroupCongr hcomm).isCyclic.1 hTcyc
  have hRcyc : IsCyclic R :=
    (Subgroup.topEquiv : (⊤ : Subgroup R) ≃* R).isCyclic.1 htop_cyc
  exact hncomm hRcyc.isMulCommutative

private theorem CFSG.theorem_4_16_large_omega_card_exp
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)]
    (hpgt : 3 < p) (hrank : groupRank R ≤ 2)
    (hOmega_large : ¬ Nat.card (omega₁ (G := R) (p := p)) ≤ p ^ 2) :
    Monoid.exponent (omega₁ (G := R) (p := p)) = p ∧
      Nat.card (omega₁ (G := R) (p := p)) = p ^ 3 := by
  classical
  let Ω : Subgroup R := omega₁ (G := R) (p := p)
  have hΩexp : Monoid.exponent Ω = p := by
    rcases proposition_4_8_b (R := R) (p := p) hpgt hrank with hExpOne | hExpP
    · haveI : Subsingleton Ω := (Monoid.exp_eq_one_iff (G := Ω)).mp hExpOne
      have hΩcard_one : Nat.card Ω = 1 := by
        simp
      have hΩ_le : Nat.card Ω ≤ p ^ 2 := by
        rw [hΩcard_one]
        exact Nat.succ_le_of_lt (pow_pos (Fact.out : Nat.Prime p).pos 2)
      exact False.elim (hOmega_large (by simpa [Ω] using hΩ_le))
    · exact hExpP
  have hΩp : IsPGroup p Ω := (Fact.out : IsPGroup p R).to_subgroup Ω
  letI : Fact (IsPGroup p Ω) := ⟨hΩp⟩
  have hΩrank : groupRank Ω ≤ 2 :=
    (groupRank_le_of_subgroup (R := R) (S := Ω)).trans hrank
  have hΩcard_le : Nat.card Ω ≤ p ^ 3 :=
    proposition_4_8_a (R := Ω) (p := p) hΩrank hΩexp
  obtain ⟨n, hn⟩ := hΩp.exists_card_eq
  have hn_ge_three : 3 ≤ n := by
    have hgt : p ^ 2 < Nat.card Ω := lt_of_not_ge (by simpa [Ω] using hOmega_large)
    rw [hn] at hgt
    have hn_gt_two : 2 < n :=
      (Nat.pow_lt_pow_iff_right (Fact.out : Nat.Prime p).one_lt).1 hgt
    omega
  have hn_le_three : n ≤ 3 := by
    rw [hn] at hΩcard_le
    exact (Nat.pow_le_pow_iff_right (Fact.out : Nat.Prime p).one_lt).1 hΩcard_le
  have hn_eq_three : n = 3 := by omega
  exact ⟨by simpa [Ω] using hΩexp, by simpa [Ω, hn_eq_three] using hn⟩

private theorem CFSG.theorem_4_16_large_omega_not_commutative
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)]
    (hrank : groupRank R ≤ 2)
    (hΩexp : Monoid.exponent (omega₁ (G := R) (p := p)) = p)
    (hΩcard : Nat.card (omega₁ (G := R) (p := p)) = p ^ 3) :
    ¬ IsMulCommutative (omega₁ (G := R) (p := p)) := by
  classical
  let Ω : Subgroup R := omega₁ (G := R) (p := p)
  intro hΩcomm
  have hΩp : IsPGroup p Ω := (Fact.out : IsPGroup p R).to_subgroup Ω
  have hΩelem : IsElementaryAbelian p Ω := {
    toIsMulCommutative := hΩcomm
    exponent_dvd_p := by
      rw [show Monoid.exponent Ω = p by simpa [Ω] using hΩexp]
  }
  letI : IsElementaryAbelian p Ω := hΩelem
  have hΩgen_three : 3 ≤ generatorRank Ω :=
    generatorRank_at_least_three_of_elementaryAbelian_card_p3_local
      (p := p) (A := Ω) (by simpa [Ω] using hΩcard)
  have hΩgen_le_rank : generatorRank Ω ≤ groupRank R :=
    generatorRank_le_groupRank_of_isPGroup_abelian_subgroup
      (R := R) (q := p) hΩp hΩcomm
  exact (by decide : ¬ 3 ≤ (2 : ℕ)) (hΩgen_three.trans (hΩgen_le_rank.trans hrank))

public theorem CFSG.isExtraspecial_of_noncommutative_card_p3_exponent_p
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
    nilpotencyClassLe_of_card_le_p_cubed (R := K) (p := p) (by rw [hKcard])
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
    have hlt := natCard_lt_of_subgroup_lt_local (G := K)
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

public theorem CFSG.derivedSubgroup_map_subtype_eq_center_map_subtype_of_isExtraspecial
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
        change derivedSeries S 1 ≤ ⊥
        exact hder_bot.le
      have hcommS : IsMulCommutative S := by
        refine ⟨⟨?_⟩⟩
        intro x y
        have hxy_mem : ⁅x, y⁆ ∈ (commutator S) :=
          Subgroup.commutator_mem_commutator
            (H₁ := (⊤ : Subgroup S)) (H₂ := (⊤ : Subgroup S)) (by simp) (by simp)
        have hxy_bot : ⁅x, y⁆ ∈ (⊥ : Subgroup S) := hcomm_le_bot hxy_mem
        have hxy_one : ⁅x, y⁆ = 1 := by simpa using hxy_bot
        exact commutatorElement_eq_one_iff_mul_comm.mp hxy_one
      letI : IsMulCommutative S := hcommS
      have hcenter_top : Subgroup.center S = ⊤ := by
        ext x
        constructor
        · intro _; simp
        · intro _
          rw [Subgroup.mem_center_iff]
          intro y
          exact ((IsMulCommutative.is_comm (M := S)).comm x y).symm
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

private theorem CFSG.omega₁_centralizer_eq_derivedSubgroup_map_of_extraspecial_omega₁
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)]
    (hΩextra : IsExtraspecial p (omega₁ (G := R) (p := p))) :
    (omega₁
        (G := Subgroup.centralizer (((omega₁ (G := R) (p := p)) : Subgroup R) : Set R))
        (p := p)).map
        (Subgroup.centralizer (((omega₁ (G := R) (p := p)) : Subgroup R) : Set R)).subtype =
      (derivedSubgroup (omega₁ (G := R) (p := p))).map
        (omega₁ (G := R) (p := p)).subtype := by
  classical
  let S : Subgroup R := omega₁ (G := R) (p := p)
  letI : IsExtraspecial p S := by
    simpa [S] using hΩextra
  let C : Subgroup R := Subgroup.centralizer ((S : Subgroup R) : Set R)
  let ΩC : Subgroup C := omega₁ (G := C) (p := p)
  let ΩCmap : Subgroup R := ΩC.map C.subtype
  let ZSmap : Subgroup R := (Subgroup.center S).map S.subtype
  have hΩC_le_S : ΩCmap ≤ S := by
    simpa [ΩCmap, ΩC, C, S] using omega₁_map_subtype_le (G := R) (p := p) C
  have hΩC_le_C : ΩCmap ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hΩC_le_ZS : ΩCmap ≤ ZSmap := by
    intro x hx
    have hxS : x ∈ S := hΩC_le_S hx
    have hxC : x ∈ C := hΩC_le_C hx
    change x ∈ (Subgroup.center S).map S.subtype
    rw [Subgroup.mem_map]
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hxC) (y : R) y.2
  have hΩC_card_map : Nat.card ΩCmap = Nat.card ΩC := by
    exact Subgroup.card_map_of_injective (K := ΩC) (f := C.subtype) C.subtype_injective
  have hZS_card_map : Nat.card ZSmap = Nat.card (Subgroup.center S) := by
    exact Subgroup.card_map_of_injective
      (K := Subgroup.center S) (f := S.subtype) S.subtype_injective
  have hΩC_le_p : Nat.card ΩC ≤ p := by
    rw [← hΩC_card_map]
    calc
      Nat.card ΩCmap ≤ Nat.card ZSmap := Subgroup.card_le_of_le hΩC_le_ZS
      _ = Nat.card (Subgroup.center S) := hZS_card_map
      _ = p := by simpa [S] using IsExtraspecial.center_order_p p S
  have hZSmap_le_C : ZSmap ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hyS
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨y, hyS⟩)
  have hZSmap_card : Nat.card ZSmap = p := by
    calc
      Nat.card ZSmap = Nat.card (Subgroup.center S) := hZS_card_map
      _ = p := by simpa [S] using IsExtraspecial.center_order_p p S
  have hC_card_ge_p : p ≤ Nat.card C := by
    rw [← hZSmap_card]
    exact Subgroup.card_le_of_le hZSmap_le_C
  have hC_nontriv : Nontrivial C :=
    Finite.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le (Fact.out : Nat.Prime p).one_lt hC_card_ge_p)
  have hCp : IsPGroup p C := (Fact.out : IsPGroup p R).to_subgroup C
  letI : Fact (IsPGroup p C) := ⟨hCp⟩
  letI : Nontrivial C := hC_nontriv
  have hΩC_ge_p : p ≤ Nat.card ΩC :=
    prime_le_natCard_omega₁_of_nontrivial_pGroup (G := C) (p := p)
  have hΩC_card : Nat.card ΩC = p := le_antisymm hΩC_le_p hΩC_ge_p
  have hΩCmap_card : Nat.card ΩCmap = p := by
    rw [hΩC_card_map, hΩC_card]
  have hΩC_eq_ZS : ΩCmap = ZSmap :=
    Subgroup.eq_of_le_of_card_ge hΩC_le_ZS (by rw [hΩCmap_card, hZSmap_card])
  have hder_eq_ZS :
      (derivedSubgroup S).map S.subtype = ZSmap :=
    derivedSubgroup_map_subtype_eq_center_map_subtype_of_isExtraspecial
      (R := R) (p := p) S
  simpa [S, C, ΩC, ΩCmap, ZSmap] using hΩC_eq_ZS.trans hder_eq_ZS.symm

private theorem CFSG.centralizer_omega₁_cyclic_of_extraspecial_omega₁
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)]
    (hpodd : p ≠ 2) (hΩextra : IsExtraspecial p (omega₁ (G := R) (p := p))) :
    IsCyclic (Subgroup.centralizer (((omega₁ (G := R) (p := p)) : Subgroup R) : Set R)) := by
  classical
  let S : Subgroup R := omega₁ (G := R) (p := p)
  letI : IsExtraspecial p S := by
    simpa [S] using hΩextra
  let C : Subgroup R := Subgroup.centralizer ((S : Subgroup R) : Set R)
  let ΩC : Subgroup C := omega₁ (G := C) (p := p)
  let ΩCmap : Subgroup R := ΩC.map C.subtype
  let ZSmap : Subgroup R := (Subgroup.center S).map S.subtype
  have hΩC_le_S : ΩCmap ≤ S := by
    simpa [ΩCmap, ΩC, C, S] using omega₁_map_subtype_le (G := R) (p := p) C
  have hΩC_le_C : ΩCmap ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hΩC_le_ZS : ΩCmap ≤ ZSmap := by
    intro x hx
    have hxS : x ∈ S := hΩC_le_S hx
    have hxC : x ∈ C := hΩC_le_C hx
    change x ∈ (Subgroup.center S).map S.subtype
    rw [Subgroup.mem_map]
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hxC) (y : R) y.2
  have hΩC_card_map : Nat.card ΩCmap = Nat.card ΩC := by
    exact Subgroup.card_map_of_injective (K := ΩC) (f := C.subtype) C.subtype_injective
  have hZS_card_map : Nat.card ZSmap = Nat.card (Subgroup.center S) := by
    exact Subgroup.card_map_of_injective
      (K := Subgroup.center S) (f := S.subtype) S.subtype_injective
  have hΩC_le_p : Nat.card ΩC ≤ p := by
    rw [← hΩC_card_map]
    calc
      Nat.card ΩCmap ≤ Nat.card ZSmap := Subgroup.card_le_of_le hΩC_le_ZS
      _ = Nat.card (Subgroup.center S) := hZS_card_map
      _ = p := by simpa [S] using IsExtraspecial.center_order_p p S
  have hZSmap_le_C : ZSmap ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hyS
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨y, hyS⟩)
  have hZSmap_card : Nat.card ZSmap = p := by
    calc
      Nat.card ZSmap = Nat.card (Subgroup.center S) := hZS_card_map
      _ = p := by simpa [S] using IsExtraspecial.center_order_p p S
  have hC_card_ge_p : p ≤ Nat.card C := by
    rw [← hZSmap_card]
    exact Subgroup.card_le_of_le hZSmap_le_C
  have hC_nontriv : Nontrivial C :=
    Finite.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le (Fact.out : Nat.Prime p).one_lt hC_card_ge_p)
  have hCp : IsPGroup p C := (Fact.out : IsPGroup p R).to_subgroup C
  letI : Fact (IsPGroup p C) := ⟨hCp⟩
  letI : Nontrivial C := hC_nontriv
  have hΩC_ge_p : p ≤ Nat.card ΩC :=
    prime_le_natCard_omega₁_of_nontrivial_pGroup (G := C) (p := p)
  have hΩC_card : Nat.card ΩC = p := le_antisymm hΩC_le_p hΩC_ge_p
  exact isCyclic_of_natCard_omega₁_eq_prime (G := C) (p := p) hpodd hΩC_card

private theorem CFSG.commutator_with_top_lt_of_nontrivial_normal_pSubgroup
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)]
    (S : Subgroup R) [S.Normal] [Nontrivial S] :
    ⁅S, (⊤ : Subgroup R)⁆ < S := by
  classical
  refine lt_of_le_of_ne (Subgroup.commutator_le_left (H₁ := S) (H₂ := (⊤ : Subgroup R))) ?_
  intro hcomm_eq
  have hnil : Group.IsNilpotent R := (Fact.out : IsPGroup p R).isNilpotent
  obtain ⟨n, hn_bot⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries (G := R)).1 hnil
  have hS_le_lower : ∀ n : ℕ, S ≤ Subgroup.lowerCentralSeries (⊤ : Subgroup R) n := by
    intro n
    induction n with
    | zero =>
        intro x _hx
        simp [Subgroup.lowerCentralSeries_zero]
    | succ n ih =>
        have hstep : ⁅S, (⊤ : Subgroup R)⁆ ≤
            Subgroup.lowerCentralSeries (⊤ : Subgroup R) (n + 1) := by
          calc
            ⁅S, (⊤ : Subgroup R)⁆ ≤
                ⁅Subgroup.lowerCentralSeries (⊤ : Subgroup R) n, (⊤ : Subgroup R)⁆ :=
              Subgroup.commutator_mono ih le_rfl
            _ = Subgroup.lowerCentralSeries (⊤ : Subgroup R) (n + 1) := by
              exact (Subgroup.lowerCentralSeries_succ (⊤ : Subgroup R) n).symm
        intro x hx
        exact hstep (by simpa [hcomm_eq] using hx)
  have hS_bot : S = ⊥ := by
    apply eq_bot_iff.2
    intro x hx
    have hx_lower : x ∈ Subgroup.lowerCentralSeries (⊤ : Subgroup R) n := hS_le_lower n hx
    simpa [hn_bot] using hx_lower
  have hS_sub : Subsingleton S := by
    constructor
    intro x y
    have hx : (x : R) = 1 := by
      have hxbot : (x : R) ∈ (⊥ : Subgroup R) := by simpa [hS_bot] using x.2
      simpa using hxbot
    have hy : (y : R) = 1 := by
      have hybot : (y : R) ∈ (⊥ : Subgroup R) := by simpa [hS_bot] using y.2
      simpa using hybot
    exact Subtype.ext (hx.trans hy.symm)
  exact (not_nontrivial_iff_subsingleton.mpr hS_sub) inferInstance

private theorem CFSG.theorem_4_16_noncentral_commutator_card
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)]
    (S : Subgroup R) [S.Normal] [IsExtraspecial p S]
    (hScard : Nat.card S = p ^ 3)
    (hnot : ¬ ⁅S, (⊤ : Subgroup R)⁆ ≤ (derivedSubgroup S).map S.subtype) :
    (derivedSubgroup S).map S.subtype ≤ ⁅S, (⊤ : Subgroup R)⁆ ∧
      ⁅S, (⊤ : Subgroup R)⁆ < S ∧
      Nat.card (↥(⁅S, (⊤ : Subgroup R)⁆ : Subgroup R)) = p ^ 2 := by
  classical
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let D : Subgroup R := (derivedSubgroup S).map S.subtype
  have hD_le_T : D ≤ T := by
    have hSS_le_T : ⁅S, S⁆ ≤ T := by
      exact Subgroup.commutator_mono le_rfl (show S ≤ (⊤ : Subgroup R) by exact le_top)
    have hD_eq : D = ⁅S, S⁆ := by
      change (derivedSubgroup S).map S.subtype = ⁅S, S⁆
      rw [derivedSubgroup, derivedSeries_one, Subgroup.map_subtype_commutator]
    simpa [hD_eq, T] using hSS_le_T
  have hD_eq_ZS :
      D = (Subgroup.center S).map S.subtype := by
    simpa [D] using
      derivedSubgroup_map_subtype_eq_center_map_subtype_of_isExtraspecial
        (R := R) (p := p) S
  have hDcard : Nat.card D = p := by
    calc
      Nat.card D = Nat.card ((Subgroup.center S).map S.subtype) := by rw [hD_eq_ZS]
      _ = Nat.card (Subgroup.center S) := by
        exact Subgroup.card_map_of_injective
          (K := Subgroup.center S) (f := S.subtype) S.subtype_injective
      _ = p := IsExtraspecial.center_order_p p S
  have hD_ne_T : D ≠ T := by
    intro hD_eq_T
    have hT_le_D : T ≤ D := by
      rw [← hD_eq_T]
    exact hnot (by simpa [D, T] using hT_le_D)
  have hD_lt_T : D < T := lt_of_le_of_ne hD_le_T hD_ne_T
  have hS_nontriv : Nontrivial S := by
    have hcard_gt : 1 < Nat.card S := by
      rw [hScard]
      exact one_lt_pow₀ (Fact.out : Nat.Prime p).one_lt (by decide)
    exact Finite.one_lt_card_iff_nontrivial.mp hcard_gt
  letI : Nontrivial S := hS_nontriv
  have hT_lt_S : T < S :=
    commutator_with_top_lt_of_nontrivial_normal_pSubgroup (R := R) (p := p) S
  have hT_p : IsPGroup p T := (Fact.out : IsPGroup p R).to_subgroup T
  obtain ⟨n, hnT⟩ := hT_p.exists_card_eq
  have hn_gt_one : 1 < n := by
    have hcard_gt : p ^ 1 < p ^ n := by
      simpa [hDcard, hnT] using natCard_lt_of_subgroup_lt_local (G := R) hD_lt_T
    exact (Nat.pow_lt_pow_iff_right (Fact.out : Nat.Prime p).one_lt).1 hcard_gt
  have hn_lt_three : n < 3 := by
    have hcard_lt : p ^ n < p ^ 3 := by
      simpa [hnT, hScard] using natCard_lt_of_subgroup_lt_local (G := R) hT_lt_S
    exact (Nat.pow_lt_pow_iff_right (Fact.out : Nat.Prime p).one_lt).1 hcard_lt
  have hn_eq_two : n = 2 := by omega
  exact ⟨by simpa [D, T] using hD_le_T, by simpa [T] using hT_lt_S,
    by simpa [T, hn_eq_two] using hnT⟩

private theorem CFSG.theorem_4_16_noncentral_centralizer_control
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)]
    (S : Subgroup R) [S.Normal] [IsExtraspecial p S]
    (hSexp : Monoid.exponent S = p) (hScard : Nat.card S = p ^ 3)
    (hnot : ¬ ⁅S, (⊤ : Subgroup R)⁆ ≤ (derivedSubgroup S).map S.subtype) :
    Nat.card (R ⧸ Subgroup.centralizer (((⁅S, (⊤ : Subgroup R)⁆ : Subgroup R)) : Set R)) = p ∧
      S ⊔ Subgroup.centralizer (((⁅S, (⊤ : Subgroup R)⁆ : Subgroup R)) : Set R) = ⊤ ∧
      IsElementaryAbelian p (⁅S, (⊤ : Subgroup R)⁆ : Subgroup R) := by
  classical
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let C_T : Subgroup R := Subgroup.centralizer ((T : Subgroup R) : Set R)
  let D : Subgroup R := (derivedSubgroup S).map S.subtype
  obtain ⟨hD_le_T, hT_lt_S, hTcard⟩ :=
    theorem_4_16_noncentral_commutator_card (R := R) (p := p) S hScard hnot
  have hT_le_S : T ≤ S := hT_lt_S.le
  have hTnormal : T.Normal := by
    dsimp [T]
    infer_instance
  letI : T.Normal := hTnormal
  have hTpow : ∀ x : T, x ^ p = 1 := by
    have hSexp_dvd : Monoid.exponent S ∣ p := by rw [hSexp]
    have hSforall : ∀ x : S, x ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hSexp_dvd
    intro x
    let xS : S := ⟨(x : R), hT_le_S x.2⟩
    have hxS : xS ^ p = 1 := hSforall xS
    apply Subtype.ext
    simpa [xS] using congrArg Subtype.val hxS
  have hTelem : IsElementaryAbelian p T :=
    isElementaryAbelian_of_card_eq_p_sq_of_forall_pow_eq_one (S := T) (p := p)
      (by simpa [T] using hTcard) hTpow
  letI : IsElementaryAbelian p T := hTelem
  have hD_eq_ZS : D = (Subgroup.center S).map S.subtype := by
    simpa [D] using
      derivedSubgroup_map_subtype_eq_center_map_subtype_of_isExtraspecial
        (R := R) (p := p) S
  let φ : R →* MulAut T := MulAut.conjNormal (H := T)
  have hker_eq_CT : φ.ker = C_T := by
    ext x
    rw [Subgroup.mem_centralizer_iff, MonoidHom.mem_ker]
    constructor
    · intro hx t ht
      have hx_apply : (φ x) ⟨t, ht⟩ = ⟨t, ht⟩ := by
        simp [hx]
      have hconj : x * t * x⁻¹ = t := by
        simpa [φ] using congrArg Subtype.val hx_apply
      have := congrArg (fun u : R => u * x) hconj
      simpa [mul_assoc] using this.symm
    · intro hx
      ext t
      have hcomm : (t : R) * x = x * t := hx t t.2
      have hconj : x * (t : R) * x⁻¹ = t := by
        calc
          x * (t : R) * x⁻¹ = ((t : R) * x) * x⁻¹ := by rw [hcomm]
          _ = t := by simp [mul_assoc]
      simpa [φ, MulAut.conjNormal_apply, MulAut.conj_apply] using hconj
  have hφ_range_p : IsPGroup p φ.range := by
    have hRtop : IsPGroup p (⊤ : Subgroup R) := by
      simpa using (Fact.out : IsPGroup p R).to_subgroup (⊤ : Subgroup R)
    rw [MonoidHom.range_eq_map]
    exact IsPGroup.map (p := p) (H := (⊤ : Subgroup R)) hRtop φ
  have hφcard_le : Nat.card φ.range ≤ p :=
    natCard_pSubgroup_mulAut_le_p_of_elementaryAbelian_card_le_p_sq
      (A := T) (p := p) hφ_range_p (by simpa [T] using hTcard.le)
  have hφrange_ne_bot : φ.range ≠ ⊥ := by
    intro hφbot
    have hT_le_ZS : T ≤ (Subgroup.center S).map S.subtype := by
      intro t ht
      let tS : S := ⟨t, hT_le_S ht⟩
      have ht_center : tS ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro s
        apply Subtype.ext
        have hsφ_one : φ (s : R) = 1 := by
          have hs_range : φ (s : R) ∈ φ.range := ⟨(s : R), rfl⟩
          have hs_bot : φ (s : R) ∈ (⊥ : Subgroup (MulAut T)) := by
            simpa [hφbot] using hs_range
          simpa using hs_bot
        let tT : T := ⟨t, ht⟩
        have hfix : (φ (s : R)) tT = tT := by simp [hsφ_one]
        have hconj : (s : R) * t * (s : R)⁻¹ = t := by
          simpa [φ, tT, MulAut.conjNormal_apply] using congrArg Subtype.val hfix
        have hmul : (s : R) * t = t * (s : R) := by
          simpa [mul_assoc] using congrArg (fun u : R => u * (s : R)) hconj
        simpa [tS] using hmul
      exact ⟨tS, ht_center, rfl⟩
    have hT_le_D : T ≤ D := by
      simpa [D, hD_eq_ZS] using hT_le_ZS
    exact hnot (by simpa [D, T] using hT_le_D)
  have hφcard_ne_one : Nat.card φ.range ≠ 1 := by
    intro hcard_one
    exact hφrange_ne_bot ((Subgroup.eq_bot_iff_card (H := φ.range)).2 hcard_one)
  have hφcard : Nat.card φ.range = p := by
    obtain ⟨n, hn⟩ := hφ_range_p.exists_card_eq
    have hn_le_one : n ≤ 1 := by
      have hpow_le' : p ^ n ≤ p := by
        rw [← hn]
        exact hφcard_le
      have hpow_le : p ^ n ≤ p ^ 1 := by simpa using hpow_le'
      exact (Nat.pow_le_pow_iff_right (Fact.out : Nat.Prime p).one_lt).1 hpow_le
    have hn_ne_zero : n ≠ 0 := by
      intro hn0
      exact hφcard_ne_one (by simpa [hn0] using hn)
    have hn_eq_one : n = 1 := by omega
    simpa [hn_eq_one] using hn
  have hquot_card : Nat.card (R ⧸ C_T) = p := by
    calc
      Nat.card (R ⧸ C_T) = Nat.card (R ⧸ φ.ker) := by rw [hker_eq_CT]
      _ = Nat.card φ.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
      _ = p := hφcard
  have hS_not_le_CT : ¬ S ≤ C_T := by
    intro hS_le_CT
    have hT_le_ZS : T ≤ (Subgroup.center S).map S.subtype := by
      intro t ht
      let tS : S := ⟨t, hT_le_S ht⟩
      have ht_center : tS ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro s
        apply Subtype.ext
        have hs_cent : (s : R) ∈ C_T := hS_le_CT s.2
        have hmul : (s : R) * t = t * (s : R) :=
          (Subgroup.mem_centralizer_iff.mp hs_cent) t ht |>.symm
        simpa [tS] using hmul
      exact ⟨tS, ht_center, rfl⟩
    have hT_le_D : T ≤ D := by
      simpa [D, hD_eq_ZS] using hT_le_ZS
    exact hnot (by simpa [D, T] using hT_le_D)
  let q : R →* R ⧸ C_T := QuotientGroup.mk' C_T
  have hSmap_ne_bot : S.map q ≠ ⊥ := by
    intro hSmap_bot
    apply hS_not_le_CT
    intro s hs
    have hsmap : q s ∈ S.map q := Subgroup.mem_map_of_mem q hs
    have hsbot : q s ∈ (⊥ : Subgroup (R ⧸ C_T)) := by simpa [hSmap_bot] using hsmap
    have hqs_one : (s : R ⧸ C_T) = 1 := by simpa [q] using hsbot
    exact (QuotientGroup.eq_one_iff (N := C_T) s).1 hqs_one
  have hSmap_top : S.map q = ⊤ := by
    have hcard_dvd : Nat.card (S.map q) ∣ Nat.card (R ⧸ C_T) :=
      Subgroup.card_subgroup_dvd_card (S.map q)
    have hcard_ne_one : Nat.card (S.map q) ≠ 1 := by
      intro hcard_one
      exact hSmap_ne_bot ((Subgroup.eq_bot_iff_card (H := S.map q)).2 hcard_one)
    have hprime_quot : Nat.Prime (Nat.card (R ⧸ C_T)) := by
      simpa [hquot_card] using (Fact.out : Nat.Prime p)
    rcases hprime_quot.eq_one_or_self_of_dvd (Nat.card (S.map q)) hcard_dvd with hcard_one | hcard_top
    · exact False.elim (hcard_ne_one hcard_one)
    · exact (Subgroup.card_eq_iff_eq_top (H := S.map q)).1 hcard_top
  have hSC_T_top : S ⊔ C_T = ⊤ := by
    apply (Subgroup.eq_top_iff' (H := S ⊔ C_T)).2
    intro r
    have hqr : q r ∈ S.map q := by simp [hSmap_top]
    rcases Subgroup.mem_map.mp hqr with ⟨s, hsS, hqs⟩
    have hsrin : s⁻¹ * r ∈ C_T := by
      apply (QuotientGroup.eq_one_iff (N := C_T) (s⁻¹ * r)).1
      calc
        q (s⁻¹ * r) = (q s)⁻¹ * q r := by simp [q, map_mul]
        _ = 1 := by rw [hqs]; simp
    exact (Subgroup.mem_sup_of_normal_left (s := S) (t := C_T)).2
      ⟨s, hsS, s⁻¹ * r, hsrin, by simp⟩
  exact ⟨by simpa [C_T, T] using hquot_card,
    by simpa [C_T, T] using hSC_T_top,
    by simpa [T] using hTelem⟩

private theorem CFSG.omega₁_centralizer_noncentral_eq_commutator_for_416
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)]
    (hpgt : 3 < p) (hrank : groupRank R ≤ 2)
    (S : Subgroup R) [S.Normal] [IsExtraspecial p S]
    (hSexp : Monoid.exponent S = p) (hScard : Nat.card S = p ^ 3)
    (hnot : ¬ ⁅S, (⊤ : Subgroup R)⁆ ≤ (derivedSubgroup S).map S.subtype) :
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    let C_T : Subgroup R := Subgroup.centralizer ((T : Subgroup R) : Set R)
    (omega₁ (G := C_T) (p := p)).map C_T.subtype = T := by
  classical
  intro T C_T
  obtain ⟨_hRmodCT_card, _hSCT_top, hTelem⟩ :=
    theorem_4_16_noncentral_centralizer_control
      (R := R) (p := p) S hSexp hScard hnot
  obtain ⟨_hD_le_T, _hT_lt_S, hTcard⟩ :=
    theorem_4_16_noncentral_commutator_card (R := R) (p := p) S hScard hnot
  have hT_elementary : IsElementaryAbelian p T := by
    simpa [T] using hTelem
  letI : IsElementaryAbelian p T := hT_elementary
  have hT_comm : IsMulCommutative T := hT_elementary.toIsMulCommutative
  have hT_le_CT : T ≤ C_T := by
    simpa [C_T] using (Subgroup.le_centralizer_iff_isMulCommutative (K := T)).2 hT_comm
  let ΩC : Subgroup C_T := omega₁ (G := C_T) (p := p)
  have hT_le_ΩCmap : T ≤ ΩC.map C_T.subtype := by
    intro t ht
    let tC : C_T := ⟨t, hT_le_CT ht⟩
    have htCpow : tC ^ p = 1 := by
      have htTpow : (⟨t, ht⟩ : T) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p T) ⟨t, ht⟩
      apply Subtype.ext
      simpa [tC] using congrArg Subtype.val htTpow
    have htCΩ : tC ∈ ΩC := by
      change tC ∈ Subgroup.closure {y : C_T | y ^ (p ^ 1) = 1}
      exact Subgroup.subset_closure (by simpa [pow_one] using htCpow)
    exact Subgroup.mem_map_of_mem C_T.subtype htCΩ
  have hΩCmap_le_T : ΩC.map C_T.subtype ≤ T := by
    intro x hx
    by_contra hxT
    rcases Subgroup.mem_map.mp hx with ⟨xC, hxCΩ, hxC_eq⟩
    have hxCpow : xC ^ p = 1 := by
      have hCTp : IsPGroup p C_T := (Fact.out : IsPGroup p R).to_subgroup C_T
      letI : Fact (IsPGroup p C_T) := ⟨hCTp⟩
      have hCTrank : groupRank C_T ≤ 2 :=
        (groupRank_le_of_subgroup (R := R) C_T).trans hrank
      rcases proposition_4_8_b (R := C_T) (p := p) hpgt hCTrank with hΩexp_one | hΩexp_p
      · have hΩsub : Subsingleton ΩC := (Monoid.exp_eq_one_iff (G := ΩC)).mp
          (by simpa [ΩC] using hΩexp_one)
        letI : Subsingleton ΩC := hΩsub
        have hx_one : x = 1 := by
          have hxC_one : xC = 1 := by
            have hxΩ_one : (⟨xC, hxCΩ⟩ : ΩC) = 1 := Subsingleton.elim _ _
            simpa using congrArg ΩC.subtype hxΩ_one
          simpa [hxC_eq] using congrArg C_T.subtype hxC_one
        exact False.elim (hxT (by simp [hx_one]))
      · have hxΩpow : (⟨xC, hxCΩ⟩ : ΩC) ^ p = 1 :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent ΩC ∣ p by
            rw [show Monoid.exponent ΩC = p by simpa [ΩC] using hΩexp_p])
            ⟨xC, hxCΩ⟩
        simpa using congrArg ΩC.subtype hxΩpow
    let Z : Subgroup R := Subgroup.zpowers x
    have hZelem : IsElementaryAbelian p Z := by
      have hxpowR : x ^ p = 1 := by
        have hxpowR' : (xC : R) ^ p = 1 := by
          simpa using congrArg C_T.subtype hxCpow
        have hxC_eq' : (xC : R) = x := hxC_eq
        simpa [hxC_eq'] using hxpowR'
      simpa [Z] using isElementaryAbelian_zpowers_of_pow_eq_one_local (p := p) (G := R) hxpowR
    letI : IsElementaryAbelian p Z := hZelem
    have hZ_le_CT : Z ≤ C_T := by
      intro z hz
      rw [Subgroup.mem_zpowers_iff] at hz
      rcases hz with ⟨n, rfl⟩
      have hxC_zpow : (xC : R) ^ n ∈ C_T := C_T.zpow_mem xC.2 n
      have hxC_eq' : (xC : R) = x := hxC_eq
      simpa [hxC_eq'] using hxC_zpow
    have hZ_le_centT : Z ≤ Subgroup.centralizer (T : Set R) := by
      simpa [C_T] using hZ_le_CT
    let U : Subgroup R := T ⊔ Z
    have hUelem : IsElementaryAbelian p U := by
      simpa [U] using
        isElementaryAbelian_sup_of_le_centralizer_local (p := p) (E := T) (C := Z)
          hZ_le_centT
    have hUp : IsPGroup p U := IsElementaryAbelian.isPGroup p U
    have hUcomm : IsMulCommutative U := hUelem.toIsMulCommutative
    have hUrank : generatorRank U ≤ 2 :=
      (generatorRank_le_groupRank_of_isPGroup_abelian_subgroup
        (R := R) (q := p) hUp hUcomm).trans hrank
    have hUcard_le : Nat.card U ≤ p ^ 2 :=
      natCard_abelian_subgroup_le_p_sq_of_rank_le_two_and_exponent_dvd_p
        (R := R) (p := p) hUp hUcomm hUrank
        (IsElementaryAbelian.exponent_dvd_p p U)
    have hT_lt_U : T < U := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro hTU_eq
      have hxU : x ∈ U := by
        exact (show Z ≤ T ⊔ Z from le_sup_right) (Subgroup.mem_zpowers x)
      have hxT' : x ∈ T := by
        rw [← hTU_eq] at hxU
        exact hxU
      exact hxT hxT'
    have hTcard' : Nat.card T = p ^ 2 := by
      simpa [T] using hTcard
    have hcard_lt : p ^ 2 < Nat.card U := by
      simpa [hTcard'] using natCard_lt_of_subgroup_lt_local (G := R) hT_lt_U
    exact (not_le_of_gt hcard_lt) hUcard_le
  exact le_antisymm hΩCmap_le_T hT_le_ΩCmap

set_option maxHeartbeats 800000 in
public theorem CFSG.theorem_4_16 {R A : Type*} [Group R] [Finite R] [Nontrivial R] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p R)]
    [MulDistribMulAction A R] [FaithfulSMul A R] (hcop : Nat.Coprime p (Nat.card A))
    (hrank : groupRank R ≤ 2) (hcomm : commutatorAction (A := A) (G := R) = ⊤)
    (hAodd : Odd (Nat.card A)) :
    3 < p ∧
      (IsMulCommutative R ∨
        ∃ R₁ R₂ : Subgroup R,
          IsCentralProduct R₁ R₂ ∧
            Nat.card R₁ = p ^ 3 ∧
            Monoid.exponent R₁ = p ∧
            ¬ IsMulCommutative R₁ ∧
            IsCyclic R₂ ∧
            (omega₁ (G := R₂) (p := p)).map R₂.subtype = (derivedSubgroup R₁).map R₁.subtype) := by
  classical
  have hpgt : 3 < p :=
    theorem_4_16_prime_gt_three (R := R) (A := A) (p := p) hpodd hcop hrank hcomm hAodd
  refine ⟨hpgt, ?_⟩
  by_cases hOmega : Nat.card (omega₁ (G := R) (p := p)) ≤ p ^ 2
  · exact Or.inl <|
      theorem_4_16_small_omega_commutative
        (R := R) (A := A) (p := p) hpodd hcop hcomm hpgt hOmega
  · obtain ⟨hΩexp, hΩcard⟩ :=
      theorem_4_16_large_omega_card_exp (R := R) (p := p) hpgt hrank hOmega
    have hΩnoncomm : ¬ IsMulCommutative (omega₁ (G := R) (p := p)) :=
      theorem_4_16_large_omega_not_commutative
        (R := R) (p := p) hrank hΩexp hΩcard
    have hΩp : IsPGroup p (omega₁ (G := R) (p := p)) :=
      (Fact.out : IsPGroup p R).to_subgroup (omega₁ (G := R) (p := p))
    letI : Fact (IsPGroup p (omega₁ (G := R) (p := p))) := ⟨hΩp⟩
    have hΩextraspecial : IsExtraspecial p (omega₁ (G := R) (p := p)) :=
      isExtraspecial_of_noncommutative_card_p3_exponent_p
        (K := omega₁ (G := R) (p := p)) (p := p) hΩcard hΩexp hΩnoncomm
    have hCcyc :
        IsCyclic (Subgroup.centralizer
          (((omega₁ (G := R) (p := p)) : Subgroup R) : Set R)) :=
      centralizer_omega₁_cyclic_of_extraspecial_omega₁
        (R := R) (p := p) hpodd hΩextraspecial
    let S : Subgroup R := omega₁ (G := R) (p := p)
    let C : Subgroup R := Subgroup.centralizer ((S : Subgroup R) : Set R)
    have hΩextraspecialS : IsExtraspecial p S := by
      simpa [S] using hΩextraspecial
    letI : IsExtraspecial p S := hΩextraspecialS
    letI : S.Characteristic := by
      simpa [S] using omega₁_characteristic (G := R) (p := p)
    have hΩC_eq_der :
        (omega₁ (G := C) (p := p)).map C.subtype =
          (derivedSubgroup S).map S.subtype := by
      simpa [S, C] using
        omega₁_centralizer_eq_derivedSubgroup_map_of_extraspecial_omega₁
          (R := R) (p := p) hΩextraspecial
    by_cases hcent_quot : ⁅S, (⊤ : Subgroup R)⁆ ≤ (derivedSubgroup S).map S.subtype
    · have hS_normal : S.Normal := by
        infer_instance
      letI : S.Normal := hS_normal
      have hC_normal : C.Normal := by
        dsimp [C]
        infer_instance
      have hSC_comm : ⁅S, C⁆ = ⊥ := by
        apply (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := S) (H₂ := C)).2
        intro s hs
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        exact ((Subgroup.mem_centralizer_iff.mp hc) s hs).symm
      have hSC_sup : S ⊔ C = ⊤ := by
        simpa [C] using lemma_4_15 (R := R) (p := p) S hcent_quot
      exact Or.inr ⟨S, C, ⟨hS_normal, hC_normal, hSC_comm, hSC_sup⟩,
        by simpa [S] using hΩcard,
        by simpa [S] using hΩexp,
        by simpa [S] using hΩnoncomm,
        by simpa [S, C] using hCcyc,
        hΩC_eq_der⟩
    · have hS_normal : S.Normal := by
        infer_instance
      letI : S.Normal := hS_normal
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      let C_T : Subgroup R := Subgroup.centralizer ((T : Subgroup R) : Set R)
      have hSexp : Monoid.exponent S = p := by
        simpa [S] using hΩexp
      obtain ⟨hRmodCT_card, hSCT_top, hTelem⟩ :=
        theorem_4_16_noncentral_centralizer_control
          (R := R) (p := p) S hSexp (by simpa [S] using hΩcard) hcent_quot
      have hT_elementary : IsElementaryAbelian p T := by
        simpa [T] using hTelem
      letI : IsElementaryAbelian p T := hT_elementary
      have hSCT_top' : S ⊔ C_T = ⊤ := by
        simpa [T, C_T] using hSCT_top
      have hRmodCT_card' : Nat.card (R ⧸ C_T) = p := by
        simpa [T, C_T] using hRmodCT_card
      have hΩCT_eq_T :
          (omega₁ (G := C_T) (p := p)).map C_T.subtype = T := by
        simpa [T, C_T] using
          omega₁_centralizer_noncentral_eq_commutator_for_416
            (R := R) (p := p) hpgt hrank S hSexp (by simpa [S] using hΩcard)
            hcent_quot
      obtain ⟨hD_le_T, hT_lt_S, hTcard⟩ :=
        theorem_4_16_noncentral_commutator_card
          (R := R) (p := p) S (by simpa [S] using hΩcard) hcent_quot
      have hT_le_S : T ≤ S := by
        simpa [T] using hT_lt_S.le
      have hT_comm : IsMulCommutative T := hT_elementary.toIsMulCommutative
      have hT_le_CT : T ≤ C_T := by
        simpa [C_T] using (Subgroup.le_centralizer_iff_isMulCommutative (K := T)).2 hT_comm
      have hΩCT_card : Nat.card (omega₁ (G := C_T) (p := p)) = p ^ 2 := by
        calc
          Nat.card (omega₁ (G := C_T) (p := p)) =
              Nat.card ((omega₁ (G := C_T) (p := p)).map C_T.subtype) := by
            exact (Subgroup.card_map_of_injective
              (K := omega₁ (G := C_T) (p := p)) (f := C_T.subtype)
              C_T.subtype_injective).symm
          _ = Nat.card T := by rw [hΩCT_eq_T]
          _ = p ^ 2 := by simpa [T] using hTcard
      have hCTp : IsPGroup p C_T := (Fact.out : IsPGroup p R).to_subgroup C_T
      letI : Fact (IsPGroup p C_T) := ⟨hCTp⟩
      have hCTmeta : IsMetacyclic C_T :=
        proposition_4_11 (R := C_T) (p := p) hpgt (by rw [hΩCT_card])
      have hS_inv : IsInvariant A R S :=
        isInvariant_of_characteristic (A := A) (G := R) S
      letI : IsInvariant A R S := hS_inv
      have htop_inv : IsInvariant A R (⊤ : Subgroup R) :=
        isInvariant_of_characteristic (A := A) (G := R) (⊤ : Subgroup R)
      letI : IsInvariant A R (⊤ : Subgroup R) := htop_inv
      have hT_inv : IsInvariant A R T := by
        simpa [T] using
          isInvariant_commutator (A := A) S (⊤ : Subgroup R)
      letI : IsInvariant A R T := hT_inv
      have hCT_inv : IsInvariant A R C_T := by
        simpa [C_T] using isInvariant_centralizer (A := A) T
      letI : IsInvariant A R C_T := hCT_inv
      letI : MulDistribMulAction A C_T := inferInstance
      have hCT_comm_action :
          IsMulCommutative (commutatorAction (A := A) (G := C_T)) :=
        theorem_4_12_a (R := C_T) (A := A) (p := p) hpodd hcop hCTmeta
      have hC_le_CT : C ≤ C_T := by
        intro c hc
        rw [Subgroup.mem_centralizer_iff] at hc ⊢
        intro t ht
        exact hc t (hT_le_S ht)
      let D : Subgroup R := (derivedSubgroup S).map S.subtype
      have hD_eq_ZS :
          D = (Subgroup.center S).map S.subtype := by
        simpa [D] using
          derivedSubgroup_map_subtype_eq_center_map_subtype_of_isExtraspecial
            (R := R) (p := p) S
      have hD_normal : D.Normal := by
        rw [hD_eq_ZS]
        letI : (Subgroup.center S).Characteristic := Subgroup.centerCharacteristic
        exact ConjAct.normal_of_characteristic_of_normal
      letI : D.Normal := hD_normal
      have hD_eq_comm : D = ⁅S, S⁆ := by
        change (derivedSubgroup S).map S.subtype = ⁅S, S⁆
        rw [derivedSubgroup, derivedSeries_one, Subgroup.map_subtype_commutator]
      have hD_inv : IsInvariant A R D := by
        rw [hD_eq_comm]
        simpa using isInvariant_commutator (A := A) S S
      letI : IsInvariant A R D := hD_inv
      have hD_le_C : D ≤ C := by
        rw [hD_eq_ZS]
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨s, hs⟩)
      have hS_not_le_CT : ¬ S ≤ C_T := by
        intro hS_le_CT
        have hT_le_D : T ≤ D := by
          rw [hD_eq_ZS]
          intro t ht
          let tS : S := ⟨t, hT_le_S ht⟩
          have ht_center : tS ∈ Subgroup.center S := by
            rw [Subgroup.mem_center_iff]
            intro s
            apply Subtype.ext
            have hs_cent : (s : R) ∈ C_T := hS_le_CT s.2
            have hmul : (s : R) * t = t * (s : R) :=
              ((Subgroup.mem_centralizer_iff.mp hs_cent) t ht).symm
            simpa [tS] using hmul
          exact ⟨tS, ht_center, rfl⟩
        exact hcent_quot (by simpa [D, T] using hT_le_D)
      have hS_action_not_le_T :
          ¬ (commutatorAction (A := A) (G := S)).map S.subtype ≤ T := by
        intro hS_action_le_T
        have hCT_normal : C_T.Normal := by
          dsimp [C_T]
          infer_instance
        letI : C_T.Normal := hCT_normal
        have hgen_mem :
            ∀ a : A, ∀ r : R, r ∈ S ⊔ C_T → r⁻¹ * (a • r) ∈ C_T := by
          intro a r hr
          rw [Subgroup.sup_eq_closure] at hr
          refine Subgroup.closure_induction
            (p := fun x _hx => x⁻¹ * (a • x) ∈ C_T) (x := r) ?mem ?one ?mul ?inv hr
          · intro x hx
            rcases hx with hxS | hxCT
            · have hxcommS :
                  (⟨x, hxS⟩ : S)⁻¹ * (a • (⟨x, hxS⟩ : S)) ∈
                    commutatorAction (A := A) (G := S) := by
                rw [commutatorAction_eq_closure]
                exact Subgroup.subset_closure ⟨a, ⟨x, hxS⟩, rfl⟩
              have hxmap :
                  x⁻¹ * (a • x) ∈
                    (commutatorAction (A := A) (G := S)).map S.subtype := by
                refine ⟨(⟨x, hxS⟩ : S)⁻¹ * (a • (⟨x, hxS⟩ : S)), hxcommS, ?_⟩
                rfl
              exact hT_le_CT (hS_action_le_T hxmap)
            · have haxCT : a • x ∈ C_T :=
                (IsInvariant.invariant (A := A) (G := R) (H := C_T) a x).1 hxCT
              exact C_T.mul_mem (C_T.inv_mem hxCT) haxCT
          · simp
          · intro x y _hx _hy hxCT hyCT
            have hconj : y⁻¹ * (x⁻¹ * (a • x)) * y ∈ C_T :=
              hCT_normal.conj_mem' (n := x⁻¹ * (a • x)) hxCT (g := y)
            have hprod : (y⁻¹ * (x⁻¹ * (a • x)) * y) * (y⁻¹ * (a • y)) ∈ C_T :=
              C_T.mul_mem hconj hyCT
            convert hprod using 1
            simp [smul_mul', mul_assoc]
          · intro x _hx hxCT
            have hcinv : (x⁻¹ * (a • x))⁻¹ ∈ C_T := C_T.inv_mem hxCT
            have hconj : (x⁻¹)⁻¹ * (x⁻¹ * (a • x))⁻¹ * x⁻¹ ∈ C_T :=
              hCT_normal.conj_mem' (n := (x⁻¹ * (a • x))⁻¹) hcinv (g := x⁻¹)
            convert hconj using 1
            simp [mul_assoc]
        have htop_le_CT : (⊤ : Subgroup R) ≤ C_T := by
          rw [← hcomm, commutatorAction_eq_closure]
          refine (Subgroup.closure_le (K := C_T)).2 ?_
          rintro x ⟨a, r, rfl⟩
          exact hgen_mem a r (by simp [hSCT_top'])
        exact hS_not_le_CT fun s _hs => htop_le_CT (by simp)
      have h_exists_alpha_s_not_T :
          ∃ a : A, ∃ s : S, (s : R)⁻¹ * (a • (s : R)) ∉ T := by
        by_contra hnone
        let Tsub : Subgroup S := T.subgroupOf S
        have hcomm_le_Tsub : commutatorAction (A := A) (G := S) ≤ Tsub := by
          rw [commutatorAction_eq_closure]
          refine (Subgroup.closure_le (K := Tsub)).2 ?_
          rintro x ⟨a, s, rfl⟩
          have hxT : ((s : R)⁻¹ * (a • (s : R))) ∈ T := by
            by_contra hxnot
            exact hnone ⟨a, s, hxnot⟩
          exact hxT
        exact hS_action_not_le_T <| by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
          exact hcomm_le_Tsub hu
      have hT_inf_C_eq_D : T ⊓ C = D := by
        apply le_antisymm
        · intro x hx
          have hxT : x ∈ T := hx.1
          have hxC : x ∈ C := hx.2
          rw [hD_eq_ZS]
          refine ⟨⟨x, hT_le_S hxT⟩, ?_, rfl⟩
          change (⟨x, hT_le_S hxT⟩ : S) ∈ Subgroup.center S
          rw [Subgroup.mem_center_iff]
          intro s
          apply Subtype.ext
          exact (Subgroup.mem_centralizer_iff.mp hxC) (s : R) s.2
        · exact le_inf (by simpa [D] using hD_le_T) hD_le_C
      have hDcard : Nat.card D = p := by
        calc
          Nat.card D = Nat.card ((Subgroup.center S).map S.subtype) := by rw [hD_eq_ZS]
          _ = Nat.card (Subgroup.center S) := by
            exact Subgroup.card_map_of_injective
              (K := Subgroup.center S) (f := S.subtype) S.subtype_injective
          _ = p := IsExtraspecial.center_order_p p S
      have hT_inf_C_card : Nat.card (↥(T ⊓ C : Subgroup R)) = p := by
        rw [hT_inf_C_eq_D, hDcard]
      have hC_normal : C.Normal := by
        dsimp [C]
        infer_instance
      letI : C.Normal := hC_normal
      let qC : R →* R ⧸ C := QuotientGroup.mk' C
      have hC_inv : IsInvariant A R C := by
        simpa [C] using isInvariant_centralizer (A := A) S
      letI : IsInvariant A R C := hC_inv
      letI : MulDistribMulAction A (R ⧸ C) :=
        quotientMulDistribMulAction (A := A) (G := R) C hC_inv
      let Q : Subgroup (R ⧸ C) := C_T.map qC
      have hQ_inv : IsInvariant A (R ⧸ C) Q := by
        simpa [Q, qC] using
          isInvariant_map_quotient (A := A) (G := R) (N := C) C_T
      letI : IsInvariant A (R ⧸ C) Q := hQ_inv
      have hTmap_card : Nat.card (T.map qC) = p := by
        let qT : T →* R ⧸ C := qC.comp T.subtype
        have hrange_eq : qT.range = T.map qC := by
          ext y
          constructor
          · rintro ⟨t, rfl⟩
            exact ⟨(t : R), t.2, rfl⟩
          · rintro ⟨t, ht, rfl⟩
            exact ⟨⟨t, ht⟩, rfl⟩
        let K : Subgroup T := (T ⊓ C).subgroupOf T
        have hker_eq : qT.ker = K := by
          ext t
          constructor
          · intro ht
            have htC : (t : R) ∈ C := by
              exact (QuotientGroup.eq_one_iff (N := C) (x := (t : R))).1
                (by simpa [qT, qC, MonoidHom.mem_ker] using ht)
            exact ⟨t.2, htC⟩
          · intro ht
            have htC : (t : R) ∈ C := ht.2
            change qT t = 1
            simpa [qT, qC, MonoidHom.mem_ker] using
              (QuotientGroup.eq_one_iff (N := C) (x := (t : R))).2 htC
        have hKcard : Nat.card K = p := by
          calc
            Nat.card K = Nat.card (↥(T ⊓ C : Subgroup R)) := by
              exact natCard_subgroupOf_eq (T ⊓ C : Subgroup R) T inf_le_left
            _ = p := hT_inf_C_card
        have hquot_card : Nat.card (T ⧸ qT.ker) = p := by
          have hmul :
              Nat.card (T ⧸ qT.ker) * p = p * p := by
            calc
              Nat.card (T ⧸ qT.ker) * p
                  = Nat.card (T ⧸ qT.ker) * Nat.card qT.ker := by rw [hker_eq, hKcard]
              _ = Nat.card T := by
                simpa [Nat.mul_comm] using
                  (Subgroup.card_eq_card_quotient_mul_card_subgroup
                    (α := T) (s := qT.ker)).symm
              _ = p ^ 2 := by simpa [T] using hTcard
              _ = p * p := by ring
          exact Nat.eq_of_mul_eq_mul_right (Fact.out : Nat.Prime p).pos hmul
        calc
          Nat.card (T.map qC) = Nat.card qT.range := by rw [hrange_eq]
          _ = Nat.card (T ⧸ qT.ker) :=
            (Nat.card_congr (QuotientGroup.quotientKerEquivRange qT).toEquiv).symm
          _ = p := hquot_card
      let Bq : Subgroup (R ⧸ C) := T.map qC
      have hBq_le_Q : Bq ≤ Q := by
        dsimp [Bq, Q]
        exact Subgroup.map_mono hT_le_CT
      have hBq_inv : IsInvariant A (R ⧸ C) Bq := by
        simpa [Bq, qC] using
          isInvariant_map_quotient (A := A) (G := R) (N := C) T
      let B : Subgroup Q := Bq.subgroupOf Q
      have hB_card : Nat.card B = p := by
        calc
          Nat.card B = Nat.card Bq := by
            exact natCard_subgroupOf_eq Bq Q hBq_le_Q
          _ = p := by simpa [Bq] using hTmap_card
      have hB_inv : IsInvariant A Q B := by
        letI : IsInvariant A (R ⧸ C) Bq := hBq_inv
        simpa [B, Bq, Q] using isInvariant_subgroupOf Bq Q
      obtain ⟨y, hyS, hy_not_T⟩ :
          ∃ y : R, y ∈ S ∧ y ∉ T :=
        SetLike.not_le_iff_exists.mp (not_le_of_gt hT_lt_S)
      let θ : C_T →* T :=
        { toFun := fun c =>
            ⟨⁅y, (c : R)⁆, by
              simpa [T] using
                (Subgroup.commutator_mem_commutator
                  (H₁ := S) (H₂ := (⊤ : Subgroup R)) hyS (by simp))⟩
          map_one' := by
            apply Subtype.ext
            simp [commutatorElement_def]
          map_mul' := by
            intro c d
            apply Subtype.ext
            have hydT : ⁅y, (d : R)⁆ ∈ T := by
              simpa [T] using
                (Subgroup.commutator_mem_commutator
                  (H₁ := S) (H₂ := (⊤ : Subgroup R)) hyS (by simp : (d : R) ∈ (⊤ : Subgroup R)))
            have hc_cent : ⁅y, (d : R)⁆ * (c : R) = (c : R) * ⁅y, (d : R)⁆ :=
              (Subgroup.mem_centralizer_iff.mp c.2) ⁅y, (d : R)⁆ hydT
            have hconj : (c : R) * ⁅y, (d : R)⁆ * (c : R)⁻¹ = ⁅y, (d : R)⁆ := by
              calc
                (c : R) * ⁅y, (d : R)⁆ * (c : R)⁻¹ =
                    (⁅y, (d : R)⁆ * (c : R)) * (c : R)⁻¹ := by rw [← hc_cent]
                _ = ⁅y, (d : R)⁆ := by simp [mul_assoc]
            calc
              ⁅y, ((c * d : C_T) : R)⁆ =
                  ⁅y, (c : R)⁆ * (c : R) * ⁅y, (d : R)⁆ * (c : R)⁻¹ := by
                simpa using commutator_mul_right y (c : R) (d : R)
              _ = ⁅y, (c : R)⁆ * ((c : R) * ⁅y, (d : R)⁆ * (c : R)⁻¹) := by
                simp [mul_assoc]
              _ = ⁅y, (c : R)⁆ * ⁅y, (d : R)⁆ := by
                rw [hconj] }
      have hCsub_le_ker_theta : C.subgroupOf C_T ≤ θ.ker := by
        intro c hc
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change ⁅y, (c : R)⁆ = 1
        have hcomm : y * (c : R) = (c : R) * y :=
          (Subgroup.mem_centralizer_iff.mp hc) y hyS
        exact (commutatorElement_eq_one_iff_mul_comm).2 hcomm
      let yS : S := ⟨y, hyS⟩
      let Tsub : Subgroup S := T.subgroupOf S
      have hT_normal : T.Normal := by
        dsimp [T]
        infer_instance
      have hTsub_normal : Tsub.Normal :=
        Subgroup.Normal.subgroupOf (G := R) (hH := hT_normal) S
      letI : Tsub.Normal := hTsub_normal
      have hTsub_card : Nat.card Tsub = p ^ 2 := by
        calc
          Nat.card Tsub = Nat.card T := by
            exact natCard_subgroupOf_eq T S hT_le_S
          _ = p ^ 2 := by simpa [T] using hTcard
      have hS_card : Nat.card S = p ^ 3 := by
        simpa [S] using hΩcard
      have hSquot_card : Nat.card (S ⧸ Tsub) = p := by
        have hmul :
            Nat.card (S ⧸ Tsub) * p ^ 2 = p * p ^ 2 := by
          calc
            Nat.card (S ⧸ Tsub) * p ^ 2 =
                Nat.card (S ⧸ Tsub) * Nat.card Tsub := by rw [hTsub_card]
            _ = Nat.card S := by
              simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup
                (α := S) (s := Tsub)).symm
            _ = p ^ 3 := hS_card
            _ = p * p ^ 2 := by ring
        exact Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : Nat.Prime p).pos 2) hmul
      let qTsub : S →* S ⧸ Tsub := QuotientGroup.mk' Tsub
      have hyq_ne_one : qTsub yS ≠ 1 := by
        intro hyq
        have hyTsub : yS ∈ Tsub :=
          (QuotientGroup.eq_one_iff (N := Tsub) (x := yS)).1 hyq
        exact hy_not_T hyTsub
      have hzy_order : orderOf (qTsub yS) = p := by
        letI : Fintype (S ⧸ Tsub) := Fintype.ofFinite (S ⧸ Tsub)
        have hpow : (qTsub yS) ^ p = 1 := by
          have hcard_pow := pow_card_eq_one (x := qTsub yS)
          have hcard_fintype : Fintype.card (S ⧸ Tsub) = p := by
            simpa [Nat.card_eq_fintype_card] using hSquot_card
          simpa [hcard_fintype] using hcard_pow
        exact orderOf_eq_prime hpow hyq_ne_one
      have hzy_top : Subgroup.zpowers (qTsub yS) = ⊤ := by
        apply (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers (qTsub yS))).1
        calc
          Nat.card (Subgroup.zpowers (qTsub yS)) = p := by
            rw [Nat.card_zpowers, hzy_order]
          _ = Nat.card (S ⧸ Tsub) := hSquot_card.symm
      have hTsub_sup_y : Tsub ⊔ Subgroup.zpowers yS = ⊤ := by
        have hmap_zpow : (Subgroup.zpowers yS).map qTsub = ⊤ := by
          rw [MonoidHom.map_zpowers, hzy_top]
        calc
          Tsub ⊔ Subgroup.zpowers yS = Subgroup.zpowers yS ⊔ Tsub := by rw [sup_comm]
          _ = Subgroup.zpowers yS ⊔ qTsub.ker := by simp [qTsub, QuotientGroup.ker_mk']
          _ = ((Subgroup.zpowers yS).map qTsub).comap qTsub := by
            symm
            simpa using (Subgroup.comap_map_eq (f := qTsub) (H := Subgroup.zpowers yS))
          _ = ⊤ := by rw [hmap_zpow]; simp
      have hker_theta_le_Csub : θ.ker ≤ C.subgroupOf C_T := by
        intro c hc
        change (c : R) ∈ C
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        let sS : S := ⟨s, hs⟩
        have hs_sup : sS ∈ Tsub ⊔ Subgroup.zpowers yS := by
          simp [hTsub_sup_y]
        rcases (Subgroup.mem_sup_of_normal_left
            (x := sS) (s := Tsub) (t := Subgroup.zpowers yS)).1 hs_sup with
          ⟨t, htTsub, z, hzpow, htz⟩
        have htheta_one : θ c = 1 := by
          simpa [MonoidHom.mem_ker] using hc
        have hyc_one : ⁅y, (c : R)⁆ = 1 := by
          simpa [θ] using congrArg Subtype.val htheta_one
        have hyc_comm : Commute y (c : R) :=
          commutatorElement_eq_one_iff_commute.mp hyc_one
        have hzc : (z : R) * (c : R) = (c : R) * (z : R) := by
          rcases Subgroup.mem_zpowers_iff.mp hzpow with ⟨k, rfl⟩
          exact (hyc_comm.zpow_left k).eq
        have htc : (t : R) * (c : R) = (c : R) * (t : R) :=
          (Subgroup.mem_centralizer_iff.mp c.2) (t : R) htTsub
        have hs_eq : s = ((t : S) * (z : S) : S) := by
          simpa [sS] using (congrArg Subtype.val htz).symm
        rw [hs_eq]
        change (((t : S) : R) * ((z : S) : R)) * (c : R) =
          (c : R) * (((t : S) : R) * ((z : S) : R))
        calc
          ((t : S) : R) * ((z : S) : R) * (c : R)
              = ((t : S) : R) * (((z : S) : R) * (c : R)) := by simp [mul_assoc]
          _ = ((t : S) : R) * ((c : R) * ((z : S) : R)) := by rw [hzc]
          _ = (((t : S) : R) * (c : R)) * ((z : S) : R) := by simp [mul_assoc]
          _ = ((c : R) * ((t : S) : R)) * ((z : S) : R) := by rw [htc]
          _ = (c : R) * (((t : S) : R) * ((z : S) : R)) := by simp [mul_assoc]
      have hker_theta_eq_Csub : θ.ker = C.subgroupOf C_T :=
        le_antisymm hker_theta_le_Csub hCsub_le_ker_theta
      have hQ_elem : IsElementaryAbelian p Q := by
        refine
          { toIsMulCommutative := ?_
            exponent_dvd_p := ?_ }
        · refine ⟨⟨fun u v => ?_⟩⟩
          rcases Subgroup.mem_map.mp u.2 with ⟨c, hcCT, hcu⟩
          rcases Subgroup.mem_map.mp v.2 with ⟨d, hdCT, hdv⟩
          apply Subtype.ext
          change (u : R ⧸ C) * (v : R ⧸ C) = (v : R ⧸ C) * (u : R ⧸ C)
          rw [← hcu, ← hdv]
          rw [← map_mul, ← map_mul]
          apply (QuotientGroup.eq_iff_div_mem).2
          let cT : C_T := ⟨c, hcCT⟩
          let dT : C_T := ⟨d, hdCT⟩
          have htheta_comm : θ (cT * dT * (dT * cT)⁻¹) = 1 := by
            calc
              θ (cT * dT * (dT * cT)⁻¹) =
                  θ cT * θ dT * (θ dT * θ cT)⁻¹ := by simp
              _ = 1 := by
                have htdc : θ dT * θ cT = θ cT * θ dT :=
                  (IsMulCommutative.is_comm (M := T)).comm (θ dT) (θ cT)
                rw [htdc]
                simp [mul_assoc]
          have hker_mem : cT * dT * (dT * cT)⁻¹ ∈ θ.ker := by
            simpa [MonoidHom.mem_ker] using htheta_comm
          have hCsub_mem : cT * dT * (dT * cT)⁻¹ ∈ C.subgroupOf C_T := by
            simpa [hker_theta_eq_Csub] using hker_mem
          change c * d / (d * c) ∈ C
          simpa [cT, dT, Subgroup.mem_subgroupOf, div_eq_mul_inv, mul_assoc] using hCsub_mem
        · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
          intro u
          rcases Subgroup.mem_map.mp u.2 with ⟨c, hcCT, hcu⟩
          apply Subtype.ext
          change (u : R ⧸ C) ^ p = 1
          rw [← hcu]
          rw [← map_pow]
          apply (QuotientGroup.eq_one_iff (N := C) (x := c ^ p)).2
          let cT : C_T := ⟨c, hcCT⟩
          have hθ_pow : θ (cT ^ p) = 1 := by
            calc
              θ (cT ^ p) = (θ cT) ^ p := by simp
              _ = 1 := by
                exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                  (IsElementaryAbelian.exponent_dvd_p p T) (θ cT)
          have hker_mem : cT ^ p ∈ θ.ker := by
            simpa [MonoidHom.mem_ker] using hθ_pow
          have hCsub_mem : cT ^ p ∈ C.subgroupOf C_T := by
            simpa [hker_theta_eq_Csub] using hker_mem
          exact hCsub_mem
      letI : IsElementaryAbelian p Q := hQ_elem
      letI : IsInvariant A Q B := hB_inv
      obtain ⟨Y, hBY, hY_inv⟩ :=
        exists_isCompl_isInvariant_of_elementaryAbelian_coprime
          (G := Q) (A := A) (p := p) hcop B
      letI : IsInvariant A Q Y := hY_inv
      let Ybar : Subgroup (R ⧸ C) := Y.map Q.subtype
      have hYbar_le_Q : Ybar ≤ Q := by
        exact Subgroup.map_subtype_le Y
      have hYbar_inv : IsInvariant A (R ⧸ C) Ybar := by
        refine ⟨?_⟩
        intro a g
        constructor
        · rintro ⟨yq, hyY, rfl⟩
          refine ⟨a • yq, (IsInvariant.invariant (A := A) (G := Q) (H := Y) a yq).1 hyY, ?_⟩
          rfl
        · rintro ⟨yq, hyY, hg⟩
          refine ⟨a⁻¹ • yq, (IsInvariant.invariant (A := A) (G := Q) (H := Y) a⁻¹ yq).1 hyY, ?_⟩
          change ((a⁻¹ • yq : Q) : R ⧸ C) = g
          calc
            ((a⁻¹ • yq : Q) : R ⧸ C) = a⁻¹ • (yq : R ⧸ C) := rfl
            _ = a⁻¹ • (a • g) := congrArg (fun z : R ⧸ C => a⁻¹ • z) hg
            _ = g := inv_smul_smul a g
      letI : IsInvariant A (R ⧸ C) Ybar := hYbar_inv
      let X : Subgroup R := Ybar.comap qC
      have hX_inv : IsInvariant A R X := by
        refine isInvariant_comap_quotient
          (A := A) (G := R) (N := C) Ybar ?_
        intro a g
        simp [MulAction.Quotient.smul_mk]
      letI : IsInvariant A R X := hX_inv
      have hC_le_X : C ≤ X := by
        simpa [X, qC, QuotientGroup.ker_mk'] using
          (Subgroup.ker_le_comap (f := qC) (H := Ybar))
      have hX_le_CT : X ≤ C_T := by
        simpa [X, Ybar, Q, qC] using
          (comap_le_of_le_map_quotient_of_le
            (G := R) (N := C) (K := C_T) hC_le_CT
            (Y := Ybar) hYbar_le_Q)
      have hT_inf_X_le_C : T ⊓ X ≤ C := by
        intro x hx
        have hxT : x ∈ T := hx.1
        have hxX : x ∈ X := hx.2
        have hxBq : qC x ∈ Bq := ⟨x, hxT, rfl⟩
        have hxYbar : qC x ∈ Ybar := by
          simpa [X] using hxX
        have hxQ : qC x ∈ Q := hBq_le_Q hxBq
        let qxQ : Q := ⟨qC x, hxQ⟩
        have hqxB : qxQ ∈ B := by
          change (qxQ : R ⧸ C) ∈ Bq
          exact hxBq
        have hqxY : qxQ ∈ Y := by
          rcases Subgroup.mem_map.mp hxYbar with ⟨yQ, hyY, hyval⟩
          have hqx_eq_y : qxQ = yQ := Subtype.ext hyval.symm
          simpa [hqx_eq_y] using hyY
        have hqx_one : qxQ = 1 :=
          (Subgroup.disjoint_def.mp hBY.disjoint) hqxB hqxY
        have hq_one : qC x = 1 := congrArg Subtype.val hqx_one
        have hxKer : x ∈ qC.ker := MonoidHom.mem_ker.2 hq_one
        simpa [qC, QuotientGroup.ker_mk'] using hxKer
      have hΩX_map_le_T :
          (omega₁ (G := X) (p := p)).map X.subtype ≤ T := by
        exact (omega₁_map_subtype_le_map_subtype_of_le
          (G := R) (p := p) (H := X) (K := C_T) hX_le_CT).trans (by rw [hΩCT_eq_T])
      have hΩX_map_le_X :
          (omega₁ (G := X) (p := p)).map X.subtype ≤ X :=
        Subgroup.map_subtype_le (omega₁ (G := X) (p := p))
      have hΩX_map_le_C :
          (omega₁ (G := X) (p := p)).map X.subtype ≤ C := by
        intro x hx
        exact hT_inf_X_le_C ⟨hΩX_map_le_T hx, hΩX_map_le_X hx⟩
      have hΩX_map_le_ΩCmap :
          (omega₁ (G := X) (p := p)).map X.subtype ≤
            (omega₁ (G := C) (p := p)).map C.subtype := by
        intro r hr
        rcases Subgroup.mem_map.mp hr with ⟨x, hxΩ, rfl⟩
        have hxΩmap :
            (x : R) ∈ (omega₁ (G := X) (p := p)).map X.subtype :=
          ⟨x, hxΩ, rfl⟩
        have hxC : (x : R) ∈ C := hΩX_map_le_C hxΩmap
        have hxT : (x : R) ∈ T := hΩX_map_le_T hxΩmap
        let xT : T := ⟨(x : R), hxT⟩
        have hxTpow : xT ^ p = 1 :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p p T) xT
        have hxRpow : (x : R) ^ p = 1 := by
          simpa [xT] using congrArg T.subtype hxTpow
        let xC : C := ⟨(x : R), hxC⟩
        have hxCΩ : xC ∈ omega₁ (G := C) (p := p) := by
          change xC ∈ Subgroup.closure {y : C | y ^ (p ^ 1) = 1}
          exact Subgroup.subset_closure (by simpa [xC, pow_one] using hxRpow)
        exact Subgroup.mem_map_of_mem C.subtype hxCΩ
      have hΩC_card_eq_p : Nat.card (omega₁ (G := C) (p := p)) = p := by
        calc
          Nat.card (omega₁ (G := C) (p := p)) =
              Nat.card ((omega₁ (G := C) (p := p)).map C.subtype) := by
            exact (Subgroup.card_map_of_injective
              (K := omega₁ (G := C) (p := p)) (f := C.subtype)
              C.subtype_injective).symm
          _ = Nat.card D := by
            rw [hΩC_eq_der]
          _ = p := hDcard
      have hΩX_card_le_p : Nat.card (omega₁ (G := X) (p := p)) ≤ p := by
        calc
          Nat.card (omega₁ (G := X) (p := p)) =
              Nat.card ((omega₁ (G := X) (p := p)).map X.subtype) := by
            exact (Subgroup.card_map_of_injective
              (K := omega₁ (G := X) (p := p)) (f := X.subtype)
              X.subtype_injective).symm
          _ ≤ Nat.card ((omega₁ (G := C) (p := p)).map C.subtype) :=
            Subgroup.card_le_of_le hΩX_map_le_ΩCmap
          _ = Nat.card (omega₁ (G := C) (p := p)) := by
            exact Subgroup.card_map_of_injective
              (K := omega₁ (G := C) (p := p)) (f := C.subtype)
              C.subtype_injective
          _ = p := hΩC_card_eq_p
      have hXp : IsPGroup p X := (Fact.out : IsPGroup p R).to_subgroup X
      letI : Fact (IsPGroup p X) := ⟨hXp⟩
      have hD_nontriv : Nontrivial D := by
        have hD_card_gt_one : 1 < Nat.card D := by
          rw [hDcard]
          exact (Fact.out : Nat.Prime p).one_lt
        exact Finite.one_lt_card_iff_nontrivial.mp hD_card_gt_one
      letI : Nontrivial D := hD_nontriv
      have hX_nontriv : Nontrivial X := by
        rcases exists_ne (1 : D) with ⟨d, hdne⟩
        refine ⟨⟨⟨(d : R), hC_le_X (hD_le_C d.2)⟩, 1, ?_⟩⟩
        intro hdX
        apply hdne
        apply Subtype.ext
        simpa using congrArg Subtype.val hdX
      letI : Nontrivial X := hX_nontriv
      have hΩX_card_ge_p : p ≤ Nat.card (omega₁ (G := X) (p := p)) :=
        prime_le_natCard_omega₁_of_nontrivial_pGroup_early (G := X) (p := p)
      have hΩX_card : Nat.card (omega₁ (G := X) (p := p)) = p :=
        le_antisymm hΩX_card_le_p hΩX_card_ge_p
      have hXcyc : IsCyclic X :=
        isCyclic_of_natCard_omega₁_eq_prime (G := X) (p := p) hpodd hΩX_card
      have hCT_le_TX : C_T ≤ T ⊔ X := by
        letI : CommGroup Q := IsMulCommutative.instCommGroup
        letI : B.Normal := Subgroup.normal_of_isMulCommutative B
        letI : T.Normal := hT_normal
        intro c hcCT
        have hcQ : qC c ∈ Q := ⟨c, hcCT, rfl⟩
        let cq : Q := ⟨qC c, hcQ⟩
        have hcq_sup : cq ∈ B ⊔ Y := by
          simp [hBY.sup_eq_top]
        rcases (Subgroup.mem_sup_of_normal_left (s := B) (t := Y) (x := cq)).1 hcq_sup with
          ⟨b, hbB, yQ, hyY, hby⟩
        have hbBq : (b : R ⧸ C) ∈ Bq := by
          exact hbB
        rcases Subgroup.mem_map.mp hbBq with ⟨t, htT, hqtb⟩
        have hyYbar : (yQ : R ⧸ C) ∈ Ybar := by
          exact ⟨yQ, hyY, rfl⟩
        rcases QuotientGroup.mk'_surjective C (yQ : R ⧸ C) with ⟨x, hxq⟩
        have hxX : x ∈ X := by
          change qC x ∈ Ybar
          simpa [qC, hxq] using hyYbar
        have hq_tx : qC (t * x) = qC c := by
          change qC t * qC x = qC c
          rw [hqtb, hxq]
          exact congrArg Subtype.val hby
        have hkC : (t * x)⁻¹ * c ∈ C := QuotientGroup.eq.mp hq_tx
        have hkX : (t * x)⁻¹ * c ∈ X := hC_le_X hkC
        refine (Subgroup.mem_sup_of_normal_left (s := T) (t := X) (x := c)).2 ?_
        refine ⟨t, htT, x * ((t * x)⁻¹ * c), X.mul_mem hxX hkX, ?_⟩
        group
      have hSX_top : S ⊔ X = ⊤ := by
        apply eq_top_iff.2
        rw [← hSCT_top']
        exact sup_le le_sup_left (hCT_le_TX.trans (sup_le_sup hT_le_S le_rfl))
      have hXS_not_le_D : ¬ ⁅X, S⁆ ≤ D := by
        intro hXS_le_D
        have hSS_le_D : ⁅S, S⁆ ≤ D := by
          have hD_eq_comm : D = ⁅S, S⁆ := by
            change (derivedSubgroup S).map S.subtype = ⁅S, S⁆
            rw [derivedSubgroup, derivedSeries_one, Subgroup.map_subtype_commutator]
          rw [hD_eq_comm]
        have hT_le_D : T ≤ D := by
          change ⁅S, (⊤ : Subgroup R)⁆ ≤ D
          rw [Subgroup.commutator_le]
          intro s hs r _hr
          have hrSX : r ∈ S ⊔ X := by
            simp [hSX_top]
          rcases (Subgroup.mem_sup_of_normal_left (s := S) (t := X) (x := r)).1 hrSX with
            ⟨s0, hs0, x0, hx0, hsx⟩
          have hss0 : ⁅s, s0⁆ ∈ D :=
            hSS_le_D (Subgroup.commutator_mem_commutator hs hs0)
          have hxs : ⁅x0, s⁆ ∈ D :=
            hXS_le_D (Subgroup.commutator_mem_commutator hx0 hs)
          have hsx0 : ⁅s, x0⁆ ∈ D := by
            simpa [commutatorElement_inv] using D.inv_mem hxs
          have hconj : s0 * ⁅s, x0⁆ * s0⁻¹ ∈ D :=
            by simpa using hD_normal.conj_mem' (n := ⁅s, x0⁆) hsx0 (g := s0⁻¹)
          have hprod : ⁅s, s0⁆ * (s0 * ⁅s, x0⁆ * s0⁻¹) ∈ D :=
            D.mul_mem hss0 hconj
          have hcomm_eq : ⁅s, r⁆ = ⁅s, s0⁆ * (s0 * ⁅s, x0⁆ * s0⁻¹) := by
            calc
              ⁅s, r⁆ = ⁅s, s0 * x0⁆ := by rw [hsx]
              _ = ⁅s, s0⁆ * s0 * ⁅s, x0⁆ * s0⁻¹ := by
                simpa using commutator_mul_right s s0 x0
              _ = ⁅s, s0⁆ * (s0 * ⁅s, x0⁆ * s0⁻¹) := by simp [mul_assoc]
          simpa [hcomm_eq] using hprod
        exact hcent_quot (by simpa [T, D] using hT_le_D)
      obtain ⟨z, hzT, hz_not_D⟩ : ∃ z : R, z ∈ T ∧ z ∉ D :=
        SetLike.not_le_iff_exists.mp (by simpa [T, D] using hcent_quot)
      let zT : T := ⟨z, hzT⟩
      let DsubT : Subgroup T := D.subgroupOf T
      have hDsubT_normal : DsubT.Normal :=
        Subgroup.Normal.subgroupOf (G := R) (hH := hD_normal) T
      letI : DsubT.Normal := hDsubT_normal
      have hDsubT_card : Nat.card DsubT = p := by
        calc
          Nat.card DsubT = Nat.card D := by
            exact natCard_subgroupOf_eq D T (by simpa [D, T] using hD_le_T)
          _ = p := hDcard
      have hT_card : Nat.card T = p ^ 2 := by
        simpa [T] using hTcard
      have hTquotD_card : Nat.card (T ⧸ DsubT) = p := by
        have hmul :
            Nat.card (T ⧸ DsubT) * p = p * p := by
          calc
            Nat.card (T ⧸ DsubT) * p =
                Nat.card (T ⧸ DsubT) * Nat.card DsubT := by rw [hDsubT_card]
            _ = Nat.card T := by
              simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup
                (α := T) (s := DsubT)).symm
            _ = p ^ 2 := hT_card
            _ = p * p := by ring
        exact Nat.eq_of_mul_eq_mul_right (Fact.out : Nat.Prime p).pos hmul
      let qDsubT : T →* T ⧸ DsubT := QuotientGroup.mk' DsubT
      have hzq_ne_one : qDsubT zT ≠ 1 := by
        intro hzq
        have hzDsubT : zT ∈ DsubT :=
          (QuotientGroup.eq_one_iff (N := DsubT) (x := zT)).1 hzq
        exact hz_not_D hzDsubT
      have hzz_order : orderOf (qDsubT zT) = p := by
        letI : Fintype (T ⧸ DsubT) := Fintype.ofFinite (T ⧸ DsubT)
        have hpow : (qDsubT zT) ^ p = 1 := by
          have hcard_pow := pow_card_eq_one (x := qDsubT zT)
          have hcard_fintype : Fintype.card (T ⧸ DsubT) = p := by
            simpa [Nat.card_eq_fintype_card] using hTquotD_card
          simpa [hcard_fintype] using hcard_pow
        exact orderOf_eq_prime hpow hzq_ne_one
      have hzz_top : Subgroup.zpowers (qDsubT zT) = ⊤ := by
        apply (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers (qDsubT zT))).1
        calc
          Nat.card (Subgroup.zpowers (qDsubT zT)) = p := by
            rw [Nat.card_zpowers, hzz_order]
          _ = Nat.card (T ⧸ DsubT) := hTquotD_card.symm
      have hDsubT_sup_z : DsubT ⊔ Subgroup.zpowers zT = ⊤ := by
        have hmap_zpow : (Subgroup.zpowers zT).map qDsubT = ⊤ := by
          rw [MonoidHom.map_zpowers, hzz_top]
        calc
          DsubT ⊔ Subgroup.zpowers zT = Subgroup.zpowers zT ⊔ DsubT := by rw [sup_comm]
          _ = Subgroup.zpowers zT ⊔ qDsubT.ker := by simp [qDsubT, QuotientGroup.ker_mk']
          _ = ((Subgroup.zpowers zT).map qDsubT).comap qDsubT := by
            symm
            simpa using (Subgroup.comap_map_eq (f := qDsubT) (H := Subgroup.zpowers zT))
          _ = ⊤ := by rw [hmap_zpow]; simp
      obtain ⟨xX, hxX_gen⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := X)).1 hXcyc
      let x : R := xX
      have hxX_mem : x ∈ X := xX.2
      have hxy_not_D : ⁅x, y⁆ ∉ D := by
        intro hxyD
        apply hXS_not_le_D
        rw [Subgroup.commutator_le]
        intro x' hx' s hs
        let qD : R →* R ⧸ D := QuotientGroup.mk' D
        have hqxy_comm : Commute (qD x) (qD y) := by
          have hqxy_one : qD ⁅x, y⁆ = 1 :=
            (QuotientGroup.eq_one_iff (N := D) (x := ⁅x, y⁆)).2 hxyD
          have hcomm_one : ⁅qD x, qD y⁆ = 1 := by
            simpa [qD, commutatorElement_def, MonoidHom.map_mul] using hqxy_one
          exact commutatorElement_eq_one_iff_commute.mp hcomm_one
        let xX' : X := ⟨x', hx'⟩
        have hx'_zpow : xX' ∈ Subgroup.zpowers xX := by
          rw [hxX_gen]
          simp
        rcases Subgroup.mem_zpowers_iff.mp hx'_zpow with ⟨m, hxm⟩
        have hx'_eq : x' = x ^ m := by
          simpa [x, xX'] using (congrArg Subtype.val hxm).symm
        let sS : S := ⟨s, hs⟩
        have hs_sup : sS ∈ Tsub ⊔ Subgroup.zpowers yS := by
          simp [hTsub_sup_y]
        rcases (Subgroup.mem_sup_of_normal_left
            (x := sS) (s := Tsub) (t := Subgroup.zpowers yS)).1 hs_sup with
          ⟨tS, htTsub, uS, huZ, htu⟩
        rcases Subgroup.mem_zpowers_iff.mp huZ with ⟨n, hun⟩
        have hs_eq : s = ((tS : S) * (uS : S) : S) := by
          simpa [sS] using (congrArg Subtype.val htu).symm
        have hu_eq : (uS : R) = y ^ n := by
          simpa [yS] using (congrArg Subtype.val hun).symm
        have hxt_comm : x' * (tS : R) = (tS : R) * x' :=
          ((Subgroup.mem_centralizer_iff.mp (hX_le_CT hx')) (tS : R) htTsub).symm
        have hxt_one : ⁅x', (tS : R)⁆ = 1 :=
          (commutatorElement_eq_one_iff_mul_comm).2 hxt_comm
        have hq_xu_comm : Commute (qD x') (qD (uS : R)) := by
          rw [hx'_eq, hu_eq, map_zpow, map_zpow]
          exact (hqxy_comm.zpow_left m).zpow_right n
        have hxuD : ⁅x', (uS : R)⁆ ∈ D := by
          have hq_one : qD ⁅x', (uS : R)⁆ = 1 := by
            simpa [qD, commutatorElement_def, MonoidHom.map_mul] using
              (commutatorElement_eq_one_iff_commute.mpr hq_xu_comm)
          exact (QuotientGroup.eq_one_iff (N := D) (x := ⁅x', (uS : R)⁆)).1 hq_one
        have hconj : (tS : R) * ⁅x', (uS : R)⁆ * (tS : R)⁻¹ ∈ D :=
          by simpa using hD_normal.conj_mem' (n := ⁅x', (uS : R)⁆) hxuD (g := (tS : R)⁻¹)
        have hcomm_eq :
            ⁅x', s⁆ = (tS : R) * ⁅x', (uS : R)⁆ * (tS : R)⁻¹ := by
          rw [hs_eq]
          change ⁅x', (tS : R) * (uS : R)⁆ =
            (tS : R) * ⁅x', (uS : R)⁆ * (tS : R)⁻¹
          calc
            ⁅x', (tS : R) * (uS : R)⁆ =
                ⁅x', (tS : R)⁆ * (tS : R) * ⁅x', (uS : R)⁆ * (tS : R)⁻¹ := by
              simpa using commutator_mul_right x' (tS : R) (uS : R)
            _ = (tS : R) * ⁅x', (uS : R)⁆ * (tS : R)⁻¹ := by
              rw [hxt_one]
              simp [mul_assoc]
        simpa [hcomm_eq] using hconj
      have hyz_mem_D : ⁅y, z⁆ ∈ D := by
        have hD_eq_comm : D = ⁅S, S⁆ := by
          change (derivedSubgroup S).map S.subtype = ⁅S, S⁆
          rw [derivedSubgroup, derivedSeries_one, Subgroup.map_subtype_commutator]
        rw [hD_eq_comm]
        exact Subgroup.commutator_mem_commutator hyS (hT_le_S hzT)
      have hyz_ne_one : ⁅y, z⁆ ≠ 1 := by
        intro hyz_one
        have hz_center : (⟨z, hT_le_S hzT⟩ : S) ∈ Subgroup.center S := by
          rw [Subgroup.mem_center_iff]
          intro s'
          let sR : R := (s' : S)
          have hs_sup : s' ∈ Tsub ⊔ Subgroup.zpowers yS := by
            simp [hTsub_sup_y]
          rcases (Subgroup.mem_sup_of_normal_left
              (x := s') (s := Tsub) (t := Subgroup.zpowers yS)).1 hs_sup with
            ⟨t0, ht0T, u0, hu0, htu0⟩
          have hzt_comm : z * (t0 : R) = (t0 : R) * z :=
            congrArg Subtype.val
              ((IsMulCommutative.is_comm (M := T)).comm ⟨z, hzT⟩ ⟨(t0 : R), ht0T⟩)
          have hzy_comm : z * y = y * z := by
            have hyz_comm : y * z = z * y :=
              (commutatorElement_eq_one_iff_mul_comm).1 hyz_one
            exact hyz_comm.symm
          have hzu_comm : z * (u0 : R) = (u0 : R) * z := by
            rcases Subgroup.mem_zpowers_iff.mp hu0 with ⟨n, rfl⟩
            exact (show Commute z y from hzy_comm).zpow_right n
          have hprod_comm : z * (((t0 : S) : R) * ((u0 : S) : R)) =
              (((t0 : S) : R) * ((u0 : S) : R)) * z := by
            calc
              z * (((t0 : S) : R) * ((u0 : S) : R)) =
                  (z * ((t0 : S) : R)) * ((u0 : S) : R) := by simp [mul_assoc]
              _ = (((t0 : S) : R) * z) * ((u0 : S) : R) := by rw [hzt_comm]
              _ = ((t0 : S) : R) * (z * ((u0 : S) : R)) := by simp [mul_assoc]
              _ = ((t0 : S) : R) * (((u0 : S) : R) * z) := by rw [hzu_comm]
              _ = (((t0 : S) : R) * ((u0 : S) : R)) * z := by simp [mul_assoc]
          apply Subtype.ext
          have hs_eq : (s' : R) = ((t0 : S) : R) * ((u0 : S) : R) := by
            simpa using congrArg Subtype.val htu0.symm
          simpa [hs_eq] using hprod_comm.symm
        have hzD : z ∈ D := by
          rw [hD_eq_ZS]
          exact ⟨⟨z, hT_le_S hzT⟩, hz_center, rfl⟩
        exact hz_not_D hzD
      have hxy_mem_T : ⁅x, y⁆ ∈ T := by
        have hyx_mem : ⁅y, x⁆ ∈ T := by
          simpa [T] using
            (Subgroup.commutator_mem_commutator
              (H₁ := S) (H₂ := (⊤ : Subgroup R)) hyS (by simp : x ∈ (⊤ : Subgroup R)))
        simpa [commutatorElement_inv] using T.inv_mem hyx_mem
      obtain ⟨α, sα, hsα_not_T⟩ := h_exists_alpha_s_not_T
      have hαyS_mem : α • y ∈ S :=
        (IsInvariant.invariant (A := A) (G := R) (H := S) α y).1 hyS
      let αyS : S := ⟨α • y, hαyS_mem⟩
      have hαy_zpow : qTsub αyS ∈ Subgroup.zpowers (qTsub yS) := by
        rw [hzy_top]
        simp
      have hαy_range :
          qTsub αyS ∈
            Finset.image (fun n : ℕ => (qTsub yS) ^ n) (Finset.range p) := by
        simpa [hzy_order] using
          (mem_zpowers_iff_mem_range_orderOf
            (x := qTsub yS) (y := qTsub αyS)).1 hαy_zpow
      rcases Finset.mem_image.mp hαy_range with ⟨j, hj_range, hj⟩
      have hj_lt : j < p := by
        simpa using Finset.mem_range.mp hj_range
      have hαzT_mem : α • z ∈ T :=
        (IsInvariant.invariant (A := A) (G := R) (H := T) α z).1 hzT
      let αzT : T := ⟨α • z, hαzT_mem⟩
      have hαz_zpow : qDsubT αzT ∈ Subgroup.zpowers (qDsubT zT) := by
        rw [hzz_top]
        simp
      have hαz_range :
          qDsubT αzT ∈
            Finset.image (fun n : ℕ => (qDsubT zT) ^ n) (Finset.range p) := by
        simpa [hzz_order] using
          (mem_zpowers_iff_mem_range_orderOf
            (x := qDsubT zT) (y := qDsubT αzT)).1 hαz_zpow
      rcases Finset.mem_image.mp hαz_range with ⟨k, hk_range, hk⟩
      have hk_lt : k < p := by
        simpa using Finset.mem_range.mp hk_range
      have hαxX_mem : α • x ∈ X :=
        (IsInvariant.invariant (A := A) (G := R) (H := X) α x).1 hxX_mem
      let αxX : X := ⟨α • x, hαxX_mem⟩
      have hαx_zpow : αxX ∈ Subgroup.zpowers xX := by
        rw [hxX_gen]
        simp
      have hαx_range :
          αxX ∈
            Finset.image (fun n : ℕ => xX ^ n) (Finset.range (orderOf xX)) := by
        simpa using
          (mem_zpowers_iff_mem_range_orderOf
            (x := xX) (y := αxX)).1 hαx_zpow
      rcases Finset.mem_image.mp hαx_range with ⟨i, hi_range, hi⟩
      have hi_lt : i < orderOf xX := by
        simpa using Finset.mem_range.mp hi_range
      have hiR : x ^ i = α • x := by
        simpa [x, αxX] using congrArg X.subtype hi
      have hD_le_X : D ≤ X := hD_le_C.trans hC_le_X
      have hyz_mem_X : ⁅y, z⁆ ∈ X := hD_le_X hyz_mem_D
      let yzX : X := ⟨⁅y, z⁆, hyz_mem_X⟩
      have hyz_powers : yzX ∈ Submonoid.powers xX := by
        exact (mem_powers_iff_mem_zpowers (G := X) (x := xX) (y := yzX)).2
          (by rw [hxX_gen]; simp)
      rcases (Submonoid.mem_powers_iff yzX xX).1 hyz_powers with ⟨n_yz, hyz_pow_x⟩
      have hyz_eq_x_pow : ⁅y, z⁆ = x ^ n_yz := by
        simpa [x, yzX] using (congrArg X.subtype hyz_pow_x).symm
      have hα_yz_eq_pow_i : α • ⁅y, z⁆ = ⁅y, z⁆ ^ i := by
        calc
          α • ⁅y, z⁆ = α • (x ^ n_yz) := by rw [hyz_eq_x_pow]
          _ = (α • x) ^ n_yz := by
            simp
          _ = (x ^ i) ^ n_yz := by rw [hiR]
          _ = x ^ (i * n_yz) := by exact (pow_mul x i n_yz).symm
          _ = x ^ (n_yz * i) := by rw [Nat.mul_comm]
          _ = (x ^ n_yz) ^ i := by exact pow_mul x n_yz i
          _ = ⁅y, z⁆ ^ i := by rw [← hyz_eq_x_pow]
      have hyz_order : orderOf ⁅y, z⁆ = p := by
        have hyz_pow_p : ⁅y, z⁆ ^ p = 1 := by
          let yzD : D := ⟨⁅y, z⁆, hyz_mem_D⟩
          have hpowD : yzD ^ p = 1 := by
            letI : Fintype D := Fintype.ofFinite D
            have hcard_pow := pow_card_eq_one (x := yzD)
            have hcard : Fintype.card D = p := by
              simpa [Nat.card_eq_fintype_card] using hDcard
            simpa [hcard] using hcard_pow
          simpa [yzD] using congrArg D.subtype hpowD
        exact orderOf_eq_prime hyz_pow_p hyz_ne_one
      have hαy_diff_mem_Tsub : ((yS ^ j)⁻¹ * αyS : S) ∈ Tsub := by
        have hq : qTsub (yS ^ j) = qTsub αyS := by
          simpa using hj
        exact QuotientGroup.eq.mp hq
      let ty : R := (y ^ j)⁻¹ * (α • y)
      have htyT : ty ∈ T := by
        change (((yS ^ j)⁻¹ * αyS : S) : R) ∈ T
        exact hαy_diff_mem_Tsub
      have hαy_eq : α • y = y ^ j * ty := by
        dsimp [ty]
        group
      have hαz_diff_mem_Dsub : ((zT ^ k)⁻¹ * αzT : T) ∈ DsubT := by
        have hq : qDsubT (zT ^ k) = qDsubT αzT := by
          simpa using hk
        exact QuotientGroup.eq.mp hq
      let dz : R := (z ^ k)⁻¹ * (α • z)
      have hdzD : dz ∈ D := by
        change (((zT ^ k)⁻¹ * αzT : T) : R) ∈ D
        exact hαz_diff_mem_Dsub
      have hdzT : dz ∈ T := hD_le_T hdzD
      have hαz_eq : α • z = z ^ k * dz := by
        dsimp [dz]
        group
      have hzkT : z ^ k ∈ T := T.pow_mem hzT k
      have hty_zk : Commute ty (z ^ k) := by
        have hcommT :
            (⟨ty, htyT⟩ : T) * ⟨z ^ k, hzkT⟩ =
              ⟨z ^ k, hzkT⟩ * ⟨ty, htyT⟩ :=
          (IsMulCommutative.is_comm (M := T)).comm ⟨ty, htyT⟩ ⟨z ^ k, hzkT⟩
        change ty * z ^ k = z ^ k * ty
        exact congrArg T.subtype hcommT
      have hty_dz : Commute ty dz := by
        have hcommT :
            (⟨ty, htyT⟩ : T) * ⟨dz, hdzT⟩ =
              ⟨dz, hdzT⟩ * ⟨ty, htyT⟩ :=
          (IsMulCommutative.is_comm (M := T)).comm ⟨ty, htyT⟩ ⟨dz, hdzT⟩
        change ty * dz = dz * ty
        exact congrArg T.subtype hcommT
      have hyjS : y ^ j ∈ S := S.pow_mem hyS j
      have hyj_dz : Commute (y ^ j) dz := by
        have hdz_map : dz ∈ (Subgroup.center S).map S.subtype := by
          simpa [hD_eq_ZS] using hdzD
        rcases Subgroup.mem_map.mp hdz_map with ⟨dS, hdScenter, hdval⟩
        have hcommS :
            dS * (⟨y ^ j, hyjS⟩ : S) = (⟨y ^ j, hyjS⟩ : S) * dS :=
          ((Subgroup.mem_center_iff.mp hdScenter) ⟨y ^ j, hyjS⟩).symm
        have hcommR : dz * y ^ j = y ^ j * dz := by
          simpa [hdval.symm] using congrArg S.subtype hcommS
        exact hcommR.symm
      have h_comm_alpha_yz : ⁅α • y, α • z⁆ = ⁅y ^ j, z ^ k⁆ := by
        rw [hαy_eq, hαz_eq]
        exact commutator_mul_factors_eq_of_commute hty_zk hty_dz hyj_dz
      let zS : S := ⟨z, hT_le_S hzT⟩
      have hyz_centerS : ⁅yS, zS⁆ ∈ Subgroup.center S := by
        have hyz_map : ⁅y, z⁆ ∈ (Subgroup.center S).map S.subtype := by
          simpa [hD_eq_ZS] using hyz_mem_D
        rcases Subgroup.mem_map.mp hyz_map with ⟨c, hc, hcval⟩
        have hc_eq : c = ⁅yS, zS⁆ := by
          apply Subtype.ext
          simpa [yS, zS, commutatorElement_def] using hcval
        simpa [hc_eq] using hc
      have h_yj_zk : ⁅y ^ j, z ^ k⁆ = ⁅y, z⁆ ^ (j * k) := by
        have hScomm :=
          commutator_pow_pow_of_mem_center (G := S) (x := yS) (y := zS) j k
            hyz_centerS
        calc
          ⁅y ^ j, z ^ k⁆ = ⁅S.subtype (yS ^ j), S.subtype (zS ^ k)⁆ := by
            rfl
          _ = S.subtype ⁅yS ^ j, zS ^ k⁆ :=
            (map_commutatorElement S.subtype (yS ^ j) (zS ^ k)).symm
          _ = S.subtype (⁅yS, zS⁆ ^ (j * k)) := congrArg S.subtype hScomm
          _ = (S.subtype ⁅yS, zS⁆) ^ (j * k) := map_pow S.subtype ⁅yS, zS⁆ (j * k)
          _ = ⁅y, z⁆ ^ (j * k) := by
            rw [map_commutatorElement]
            rfl
      have hα_yz_comm : α • ⁅y, z⁆ = ⁅α • y, α • z⁆ := by
        calc
          α • ⁅y, z⁆ = (MulDistribMulAction.toMulAut A R α) ⁅y, z⁆ := rfl
          _ = ⁅(MulDistribMulAction.toMulAut A R α) y,
                (MulDistribMulAction.toMulAut A R α) z⁆ :=
            map_commutatorElement (MulDistribMulAction.toMulAut A R α) y z
          _ = ⁅α • y, α • z⁆ := rfl
      have hyz_pow_i_eq_jk : ⁅y, z⁆ ^ i = ⁅y, z⁆ ^ (j * k) := by
        calc
          ⁅y, z⁆ ^ i = α • ⁅y, z⁆ := hα_yz_eq_pow_i.symm
          _ = ⁅α • y, α • z⁆ := hα_yz_comm
          _ = ⁅y ^ j, z ^ k⁆ := h_comm_alpha_yz
          _ = ⁅y, z⁆ ^ (j * k) := h_yj_zk
      have hi_eq_jk_zmod : (i : ZMod p) = (j * k : ZMod p) :=
        by simpa using zmod_natCast_eq_of_pow_eq_of_orderOf hyz_order hyz_pow_i_eq_jk
      have hDsubT_inv : IsInvariant A T DsubT := by
        simpa [DsubT] using isInvariant_subgroupOf D T
      letI : IsInvariant A T DsubT := hDsubT_inv
      letI : MulDistribMulAction A (T ⧸ DsubT) :=
        quotientMulDistribMulAction (A := A) (G := T) DsubT hDsubT_inv
      let xyT : T := ⟨⁅x, y⁆, hxy_mem_T⟩
      have hxyq_ne_one : qDsubT xyT ≠ 1 := by
        intro hxyq
        have hxyDsub : xyT ∈ DsubT :=
          (QuotientGroup.eq_one_iff (N := DsubT) (x := xyT)).1 hxyq
        exact hxy_not_D hxyDsub
      have hxyq_order : orderOf (qDsubT xyT) = p := by
        letI : Fintype (T ⧸ DsubT) := Fintype.ofFinite (T ⧸ DsubT)
        have hpow : (qDsubT xyT) ^ p = 1 := by
          have hcard_pow := pow_card_eq_one (x := qDsubT xyT)
          have hcard_fintype : Fintype.card (T ⧸ DsubT) = p := by
            simpa [Nat.card_eq_fintype_card] using hTquotD_card
          simpa [hcard_fintype] using hcard_pow
        exact orderOf_eq_prime hpow hxyq_ne_one
      have hα_qz_eq_pow_k : α • qDsubT zT = (qDsubT zT) ^ k := by
        calc
          α • qDsubT zT = qDsubT (α • zT) := by
            simp [qDsubT, MulAction.Quotient.smul_mk]
          _ = qDsubT αzT := by
            congr
          _ = (qDsubT zT) ^ k := hk.symm
      have hxyq_zpow : qDsubT xyT ∈ Subgroup.zpowers (qDsubT zT) := by
        rw [hzz_top]
        simp
      have hxyq_powers : qDsubT xyT ∈ Submonoid.powers (qDsubT zT) :=
        (mem_powers_iff_mem_zpowers
          (G := T ⧸ DsubT) (x := qDsubT zT) (y := qDsubT xyT)).2 hxyq_zpow
      rcases (Submonoid.mem_powers_iff (qDsubT xyT) (qDsubT zT)).1 hxyq_powers with
        ⟨n_xy, hxyq_eq_zpow⟩
      have hα_qxy_eq_pow_k : α • qDsubT xyT = (qDsubT xyT) ^ k := by
        calc
          α • qDsubT xyT = α • ((qDsubT zT) ^ n_xy) := by rw [hxyq_eq_zpow]
          _ = (α • qDsubT zT) ^ n_xy := by
            rw [smul_pow']
          _ = ((qDsubT zT) ^ k) ^ n_xy := by rw [hα_qz_eq_pow_k]
          _ = (qDsubT zT) ^ (k * n_xy) := by exact (pow_mul (qDsubT zT) k n_xy).symm
          _ = (qDsubT zT) ^ (n_xy * k) := by rw [Nat.mul_comm]
          _ = ((qDsubT zT) ^ n_xy) ^ k := by exact pow_mul (qDsubT zT) n_xy k
          _ = (qDsubT xyT) ^ k := by rw [← hxyq_eq_zpow]
      have hST_le_D : ⁅S, T⁆ ≤ D := by
        calc
          ⁅S, T⁆ ≤ ⁅S, S⁆ := Subgroup.commutator_mono le_rfl hT_le_S
          _ = D := hD_eq_comm.symm
      have hRT_mem_D : ∀ r : R, ∀ t ∈ T, ⁅r, t⁆ ∈ D := by
        intro r t ht
        have hrSX : r ∈ S ⊔ X := by
          simp [hSX_top]
        rcases (Subgroup.mem_sup_of_normal_left (x := r) (s := S) (t := X)).1 hrSX with
          ⟨s0, hs0, x0, hx0, hsx⟩
        have hs0tD : ⁅s0, t⁆ ∈ D :=
          hST_le_D (Subgroup.commutator_mem_commutator hs0 ht)
        have hx0t_one : ⁅x0, t⁆ = 1 := by
          have hcent : t * x0 = x0 * t :=
            (Subgroup.mem_centralizer_iff.mp (hX_le_CT hx0)) t ht
          exact (commutatorElement_eq_one_iff_mul_comm).2 hcent.symm
        have hcomm_eq : ⁅r, t⁆ = ⁅s0, t⁆ := by
          rw [← hsx, commutator_mul_left, hx0t_one]
          simp
        simpa [hcomm_eq] using hs0tD
      have hxi_ty_one : ⁅x ^ i, ty⁆ = 1 := by
        have hxiX : x ^ i ∈ X := X.pow_mem hxX_mem i
        have hcent : ty * (x ^ i) = (x ^ i) * ty :=
          (Subgroup.mem_centralizer_iff.mp (hX_le_CT hxiX)) ty htyT
        exact (commutatorElement_eq_one_iff_mul_comm).2 hcent.symm
      have hα_xy_eq_xiyj : α • ⁅x, y⁆ = ⁅x ^ i, y ^ j⁆ := by
        have hα_xy_comm : α • ⁅x, y⁆ = ⁅α • x, α • y⁆ := by
          calc
            α • ⁅x, y⁆ = (MulDistribMulAction.toMulAut A R α) ⁅x, y⁆ := rfl
            _ = ⁅(MulDistribMulAction.toMulAut A R α) x,
                  (MulDistribMulAction.toMulAut A R α) y⁆ :=
              map_commutatorElement (MulDistribMulAction.toMulAut A R α) x y
            _ = ⁅α • x, α • y⁆ := rfl
        calc
          α • ⁅x, y⁆ = ⁅α • x, α • y⁆ := hα_xy_comm
          _ = ⁅x ^ i, y ^ j * ty⁆ := by rw [← hiR, hαy_eq]
          _ = ⁅x ^ i, y ^ j⁆ := by
            rw [commutator_mul_right, hxi_ty_one]
            simp [mul_assoc]
      let qD : R →* R ⧸ D := QuotientGroup.mk' D
      have hqDxy_center : ⁅qD x, qD y⁆ ∈ Subgroup.center (R ⧸ D) := by
        rw [Subgroup.mem_center_iff]
        intro rbar
        rcases QuotientGroup.mk'_surjective D rbar with ⟨r, rfl⟩
        have hmemD : ⁅r, ⁅x, y⁆⁆ ∈ D := hRT_mem_D r ⁅x, y⁆ hxy_mem_T
        have hqone : qD ⁅r, ⁅x, y⁆⁆ = 1 :=
          (QuotientGroup.eq_one_iff (N := D) (x := ⁅r, ⁅x, y⁆⁆)).2 hmemD
        have hcomm_one : ⁅qD r, ⁅qD x, qD y⁆⁆ = 1 := by
          simpa [qD, map_commutatorElement] using hqone
        exact (commutatorElement_eq_one_iff_mul_comm).1 hcomm_one
      have hqD_xiyj :
          qD ⁅x ^ i, y ^ j⁆ = qD (⁅x, y⁆ ^ (i * j)) := by
        have hpow :=
          commutator_pow_pow_of_mem_center (G := R ⧸ D) (x := qD x) (y := qD y) i j
            hqDxy_center
        calc
          qD ⁅x ^ i, y ^ j⁆ = ⁅qD (x ^ i), qD (y ^ j)⁆ :=
            map_commutatorElement qD (x ^ i) (y ^ j)
          _ = ⁅(qD x) ^ i, (qD y) ^ j⁆ := by rw [map_pow, map_pow]
          _ = ⁅qD x, qD y⁆ ^ (i * j) := hpow
          _ = qD (⁅x, y⁆ ^ (i * j)) := by rw [map_pow, map_commutatorElement]
      have hqD_alpha_xy :
          qD (α • ⁅x, y⁆) = qD (⁅x, y⁆ ^ (i * j)) := by
        rw [hα_xy_eq_xiyj]
        exact hqD_xiyj
      have hdiff_alpha_xy_D : (α • ⁅x, y⁆)⁻¹ * ⁅x, y⁆ ^ (i * j) ∈ D :=
        QuotientGroup.eq.mp hqD_alpha_xy
      have hα_qxy_eq_pow_ij : α • qDsubT xyT = (qDsubT xyT) ^ (i * j) := by
        calc
          α • qDsubT xyT = qDsubT (α • xyT) := by
            simp [qDsubT, MulAction.Quotient.smul_mk]
          _ = qDsubT (xyT ^ (i * j)) := by
            apply (QuotientGroup.eq).2
            change (((α • xyT)⁻¹ * xyT ^ (i * j) : T) : R) ∈ D
            change ((α • ⁅x, y⁆)⁻¹ * ⁅x, y⁆ ^ (i * j)) ∈ D
            exact hdiff_alpha_xy_D
          _ = (qDsubT xyT) ^ (i * j) := by
            simp
      have hxy_pow_k_eq_ij : (qDsubT xyT) ^ k = (qDsubT xyT) ^ (i * j) := by
        rw [← hα_qxy_eq_pow_k, hα_qxy_eq_pow_ij]
      have hk_eq_ij_zmod : (k : ZMod p) = (i * j : ZMod p) :=
        by simpa using zmod_natCast_eq_of_pow_eq_of_orderOf hxyq_order hxy_pow_k_eq_ij
      have hyz_pow_i_ne_one : ⁅y, z⁆ ^ i ≠ 1 := by
        intro hpow
        have hα_yz_one : α • ⁅y, z⁆ = 1 := by
          simpa [hα_yz_eq_pow_i] using hpow
        have hyz_one : ⁅y, z⁆ = 1 := by
          have hback := congrArg (fun u : R => α⁻¹ • u) hα_yz_one
          simpa [smul_smul] using hback
        exact hyz_ne_one hyz_one
      have hi_ne_zero : (i : ZMod p) ≠ 0 := by
        intro hi_zero
        have hmod : i ≡ 0 [MOD p] := by
          exact (ZMod.natCast_eq_natCast_iff i 0 p).1 (by simpa using hi_zero)
        have hpow : ⁅y, z⁆ ^ i = 1 := by
          have hpow0 : ⁅y, z⁆ ^ i = ⁅y, z⁆ ^ 0 := by
            exact (pow_eq_pow_iff_modEq (x := ⁅y, z⁆) (m := 0) (n := i)).2
              (by simpa [hyz_order] using hmod)
          simpa using hpow0
        exact hyz_pow_i_ne_one hpow
      have hi_eq_i_j_sq :
          (i : ZMod p) = (i : ZMod p) * ((j : ZMod p) * (j : ZMod p)) := by
        calc
          (i : ZMod p) = (j : ZMod p) * (k : ZMod p) := hi_eq_jk_zmod
          _ = (j : ZMod p) * ((i : ZMod p) * (j : ZMod p)) := by rw [hk_eq_ij_zmod]
          _ = (i : ZMod p) * ((j : ZMod p) * (j : ZMod p)) := by ring
      have hj_sq_eq_one : (j : ZMod p) * (j : ZMod p) = 1 := by
        apply mul_left_cancel₀ hi_ne_zero
        calc
          (i : ZMod p) * ((j : ZMod p) * (j : ZMod p)) = (i : ZMod p) := hi_eq_i_j_sq.symm
          _ = (i : ZMod p) * 1 := by rw [mul_one]
      have hTsub_inv : IsInvariant A S Tsub := by
        simpa [Tsub] using isInvariant_subgroupOf T S
      letI : IsInvariant A S Tsub := hTsub_inv
      letI : MulDistribMulAction A (S ⧸ Tsub) :=
        quotientMulDistribMulAction (A := A) (G := S) Tsub hTsub_inv
      have hα_qy_eq_pow_j : α • qTsub yS = (qTsub yS) ^ j := by
        calc
          α • qTsub yS = qTsub (α • yS) := by
            simp [qTsub, MulAction.Quotient.smul_mk]
          _ = qTsub αyS := by
            congr
          _ = (qTsub yS) ^ j := hj.symm
      have hj_sq_mod : j * j ≡ 1 [MOD p] := by
        exact (ZMod.natCast_eq_natCast_iff (j * j) 1 p).1 (by simpa using hj_sq_eq_one)
      have hqy_j_sq : (qTsub yS) ^ (j * j) = qTsub yS := by
        have hpow : (qTsub yS) ^ (j * j) = (qTsub yS) ^ 1 := by
          exact (pow_eq_pow_iff_modEq (x := qTsub yS) (m := 1) (n := j * j)).2
            (by simpa [hzy_order] using hj_sq_mod)
        simpa using hpow
      have hα2_qy_fixed : (α ^ 2) • qTsub yS = qTsub yS := by
        calc
          (α ^ 2) • qTsub yS = α • (α • qTsub yS) := by
            simp [pow_two, smul_smul]
          _ = α • ((qTsub yS) ^ j) := by rw [hα_qy_eq_pow_j]
          _ = (α • qTsub yS) ^ j := by rw [smul_pow']
          _ = ((qTsub yS) ^ j) ^ j := by rw [hα_qy_eq_pow_j]
          _ = (qTsub yS) ^ (j * j) := by exact (pow_mul (qTsub yS) j j).symm
          _ = qTsub yS := hqy_j_sq
      have hα2_fixed_all : ∀ s : S, (α ^ 2) • qTsub s = qTsub s := by
        intro s
        have hs_zpow : qTsub s ∈ Subgroup.zpowers (qTsub yS) := by
          rw [hzy_top]
          simp
        have hs_powers : qTsub s ∈ Submonoid.powers (qTsub yS) :=
          (mem_powers_iff_mem_zpowers
            (G := S ⧸ Tsub) (x := qTsub yS) (y := qTsub s)).2 hs_zpow
        rcases (Submonoid.mem_powers_iff (qTsub s) (qTsub yS)).1 hs_powers with
          ⟨n, hn⟩
        calc
          (α ^ 2) • qTsub s = (α ^ 2) • ((qTsub yS) ^ n) := by rw [hn]
          _ = ((α ^ 2) • qTsub yS) ^ n := by rw [smul_pow']
          _ = (qTsub yS) ^ n := by rw [hα2_qy_fixed]
          _ = qTsub s := hn
      have hα_mem_zpowers_sq : α ∈ Subgroup.zpowers (α ^ 2) := by
        rw [mem_zpowers_pow_iff]
        have horder_odd : Odd (orderOf α) :=
          Odd.of_dvd_nat hAodd (orderOf_dvd_natCard α)
        have hcop_two : Nat.Coprime 2 (orderOf α) :=
          (Nat.coprime_two_left).2 horder_odd
        simpa [Nat.Coprime] using hcop_two
      have hα_fixed_all : ∀ s : S, α • qTsub s = qTsub s := by
        intro s
        exact smul_eq_self_of_mem_zpowers hα_mem_zpowers_sq (hα2_fixed_all s)
      have hα_sα_fixed : qTsub sα = qTsub (α • sα) := by
        calc
          qTsub sα = α • qTsub sα := (hα_fixed_all sα).symm
          _ = qTsub (α • sα) := by
            simp [qTsub, MulAction.Quotient.smul_mk]
      have hsα_T : (sα : R)⁻¹ * α • (sα : R) ∈ T := by
        have hsα_Tsub : sα⁻¹ * (α • sα) ∈ Tsub :=
          QuotientGroup.eq.mp hα_sα_fixed
        change ((sα⁻¹ * (α • sα) : S) : R) ∈ T
        exact hsα_Tsub
      exact False.elim (hsα_not_T hsα_T)
