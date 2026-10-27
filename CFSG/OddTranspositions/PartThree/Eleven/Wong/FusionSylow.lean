module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.FusionE
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.Basic
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.SylowLift

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup

namespace SwapData

variable {G : Type} [Group G] (D : SwapData G)

private theorem wongS_t_mem : D.t ∈ D.S :=
  zpowers_le.mpr (subset_closure (by simp)) D.t_mem_zpowers_h1

private theorem wongS_h1_mem : D.h1 ∈ D.S := subset_closure (by simp)
private theorem wongS_h2_mem : D.h2 ∈ D.S := subset_closure (by simp)
private theorem wongS_c1_mem : D.c1 ∈ D.S := subset_closure (by simp)
private theorem wongS_c2_mem : D.c2 ∈ D.S := subset_closure (by simp)
private theorem wongS_u_mem : D.u ∈ D.S := subset_closure (by simp)

private theorem wongS_orderOf_cM : orderOf cM = 4 := by
  apply (orderOf_eq_iff (n := 4) (by norm_num)).mpr
  constructor
  · decide
  · intro m hm0 hm4
    interval_cases m <;> decide

private theorem wongS_orderOf_c1 : orderOf D.c1 = 4 := by
  rw [show D.c1 = D.i1 cM from rfl, orderOf_injective D.i1 D.inj1 cM]
  exact wongS_orderOf_cM

private theorem wongS_two_pow_factorization_14400 : 2 ^ (14400 : ℕ).factorization 2 = 64 := by
  rw [Nat.factorization_def 14400 Nat.prime_two]
  have h1 : (14400 : ℕ) = 2 ^ 6 * 225 := by norm_num
  rw [h1, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 225)]
  norm_num

theorem centralizer_t_inf_centralizer_v_le_S [Finite G] :
    centralizer {D.t} ⊓ centralizer {D.v} ≤ D.S := by
  rw [D.centralizer_t_inf_centralizer_v]
  refine (closure_le _).mpr ?_
  rintro g (rfl | rfl | rfl | rfl)
  · exact mul_mem (wongS_t_mem D) (wongS_u_mem D)
  · exact wongS_h1_mem D
  · exact wongS_h2_mem D
  · exact mul_mem (wongS_c1_mem D) (wongS_c2_mem D)

theorem card_S [Finite G] : Nat.card D.S = 64 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Tv : Subgroup G := centralizer {D.t} ⊓ centralizer {D.v}
  have hTv_eq : Tv = closure {D.r, D.h1, D.h2, D.w} := by
    show centralizer {D.t} ⊓ centralizer {D.v} = closure {D.r, D.h1, D.h2, D.w}
    exact D.centralizer_t_inf_centralizer_v
  have hTv_card : Nat.card Tv = 32 := by
    show Nat.card (↥(centralizer {D.t} ⊓ centralizer {D.v} : Subgroup G)) = 32
    exact D.card_centralizer_t_inf_centralizer_v
  have hc1invN : D.c1⁻¹ ∈ normalizer (Tv : Set G) := by
    refine Subgroup.mem_normalizer_fintype ?_
    intro x hx
    have hx' : x ∈ centralizer {D.t} ⊓ centralizer {D.v} := hx
    obtain ⟨hxt, hxv⟩ := mem_inf.mp hx'
    have hyt : Commute (D.c1⁻¹ * x * D.c1) D.t := by
      have h := ((commute_iff_eq x D.t).mpr (mem_centralizer_singleton_iff.mp hxt)).conj D.c1⁻¹
      simpa only [inv_inv, D.conj_c1_eb.1] using h
    have hyv' : Commute (D.c1⁻¹ * x * D.c1) (D.t * D.v) := by
      have h := ((commute_iff_eq x D.v).mpr (mem_centralizer_singleton_iff.mp hxv)).conj D.c1⁻¹
      simpa only [inv_inv, D.conj_c1_eb.2.2.1] using h
    have hyv : Commute (D.c1⁻¹ * x * D.c1) D.v := by
      have h := hyt.mul_right hyv'
      simpa only [D.t_mul_t_mul] using h
    have hmem : D.c1⁻¹ * x * D.c1 ∈ centralizer {D.t} ⊓ centralizer {D.v} :=
      mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hyt.eq,
        mem_centralizer_singleton_iff.mpr hyv.eq⟩
    rw [show (D.c1⁻¹)⁻¹ = D.c1 from inv_inv _]
    exact hmem
  have hc1N : D.c1 ∈ normalizer (Tv : Set G) := by
    simpa only [inv_inv] using inv_mem hc1invN
  have hTv2 : IsPGroup 2 Tv := by
    refine IsPGroup.of_card (n := 5) ?_
    rw [hTv_card]
    norm_num
  have hzp : IsPGroup 2 (zpowers D.c1) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers, wongS_orderOf_c1 D]
    norm_num
  have hSup2 : IsPGroup 2 (↥(Tv ⊔ zpowers D.c1 : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_left' hTv2 hzp (zpowers_le.mpr hc1N)
  have hS_le : D.S ≤ Tv ⊔ zpowers D.c1 := by
    rw [hTv_eq]
    refine (closure_le _).mpr ?_
    rintro g (rfl | rfl | rfl | rfl | rfl)
    · exact mem_sup_left (subset_closure (by simp))
    · exact mem_sup_right (mem_zpowers D.c1)
    · exact mem_sup_left (subset_closure (by simp))
    · have hc2 : D.c2 = D.c1⁻¹ * D.w := by
        rw [show D.w = D.c1 * D.c2 from rfl]
        group
      rw [hc2]
      exact mul_mem (mem_sup_right (inv_mem (mem_zpowers D.c1)))
        (mem_sup_left (subset_closure (by simp)))
    · have ht : D.t ∈ closure {D.r, D.h1, D.h2, D.w} :=
        zpowers_le.mpr (subset_closure (by simp)) D.t_mem_zpowers_h1
      have hr : D.r ∈ closure {D.r, D.h1, D.h2, D.w} := subset_closure (by simp)
      have hu : D.u = D.t * D.r := by
        rw [show D.r = D.t * D.u from rfl, ← mul_assoc, D.t_mul_t, one_mul]
      rw [hu]
      exact mul_mem (mem_sup_left ht) (mem_sup_left hr)
  have hS2 : IsPGroup 2 D.S := hSup2.to_le hS_le
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hle : Tv ≤ D.S := by
    show centralizer {D.t} ⊓ centralizer {D.v} ≤ D.S
    exact centralizer_t_inf_centralizer_v_le_S D
  have hc1not : D.c1 ∉ Tv := by
    intro hc1Tv
    have hc1v : D.c1 * D.v = D.v * D.c1 :=
      mem_centralizer_singleton_iff.mp
        (mem_inf.mp (show D.c1 ∈ centralizer {D.t} ⊓ centralizer {D.v} from hc1Tv)).2
    have hconj : D.c1⁻¹ * D.v * D.c1 = D.v := by
      rw [mul_assoc, ← hc1v, inv_mul_cancel_left]
    have htv : D.t * D.v = D.v := by
      rw [← D.conj_c1_eb.2.2.1, hconj]
    have ht1 : D.t = 1 := by
      calc D.t = D.t * 1 := (mul_one _).symm
        _ = D.t * (D.v * D.v) := by rw [D.v_mul_v]
        _ = (D.t * D.v) * D.v := by rw [mul_assoc]
        _ = D.v * D.v := by rw [htv]
        _ = 1 := D.v_mul_v
    have hord : orderOf D.t = 2 := D.orderOf_t
    rw [ht1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hnot : ¬ D.S ≤ Tv := fun h => hc1not (h (wongS_c1_mem D))
  have hlt : Tv < D.S := lt_of_le_not_ge hle hnot
  have hcard_lt : Nat.card Tv < Nat.card D.S := Subgroup.card_lt_of_lt hlt
  rw [hTv_card, hk] at hcard_lt
  have hk_ge : 6 ≤ k := by
    by_contra h
    have hk5 : k ≤ 5 := by omega
    have hle2 : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hk5
    norm_num at hle2
    omega
  have hk_le : k ≤ 6 := by
    by_contra h
    have h7 : 7 ≤ k := by omega
    have hdvd : 2 ^ k ∣ 14400 := by
      have h := Subgroup.card_dvd_of_le D.S_le_centralizer_t
      rw [hk, D.hyp.card_centralizer] at h
      exact h
    have hdvd7 : 2 ^ 7 ∣ 2 ^ k := pow_dvd_pow 2 h7
    have hcontra : (2 : ℕ) ^ 7 ∣ 14400 := hdvd7.trans hdvd
    norm_num at hcontra
  have hk6 : k = 6 := le_antisymm hk_le hk_ge
  rw [hk, hk6]
  norm_num

theorem isSylow_S [Finite G] : ∃ P : Sylow 2 G, (P : Subgroup G) = D.S := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : CFSG.ABGLocalTools.IsSylowOf 2 D.S (centralizer {D.t}) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card D.S_le_centralizer_t ?_
    rw [card_S D, D.hyp.card_centralizer]
    exact wongS_two_pow_factorization_14400.symm
  have htS : D.t ∈ D.S := wongS_t_mem D
  have hchar : ((zpowers D.t).subgroupOf D.S).Characteristic := by
    rw [← D.center_S]
    exact Subgroup.centerCharacteristic
  have hN : normalizer (D.S : Set G) ≤ centralizer {D.t} :=
    normalizer_le_centralizer_of_characteristic D.orderOf_t htS hchar
  have htop : CFSG.ABGLocalTools.IsSylowOf 2 D.S ⊤ :=
    (D.hyp.isSylowOf_top_of_normalizer_le hU hN).1
  have hcardG : Nat.card D.S = 2 ^ (Nat.card G).factorization 2 := by
    rw [← Subgroup.card_top (G := G)]
    exact CFSG.ABGLocalTools.IsSylowOf.card_eq htop
  refine ⟨Sylow.ofCard D.S hcardG, ?_⟩
  rw [Sylow.coe_ofCard]

include D in
theorem factorization_card_two [Finite G] : (Nat.card G).factorization 2 = 6 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := D.isSylow_S
  have hPcard : Nat.card P = 2 ^ (Nat.card G).factorization 2 := Sylow.card_eq_multiplicity P
  have hpow : 2 ^ (Nat.card G).factorization 2 = 2 ^ 6 := by
    rw [← hPcard]
    rw [show Nat.card P = 64 by rw [hP]; exact D.card_S]
    norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow

end SwapData

end CFSG.OddTranspositions.PartThree.Wong
