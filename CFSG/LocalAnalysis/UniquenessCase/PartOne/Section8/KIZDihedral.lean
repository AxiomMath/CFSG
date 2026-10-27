module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
import CFSG.GroupTheory.SupMulCommutative
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.GroupTheory.IndexNormal
import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ

open Subgroup

variable {X : Type} [Group X] [Finite X]

private theorem mem_dihedralRotations_of_pow_nine {g : DihedralGroup 9} (h : g ^ 9 = 1) :
    g ∈ TauCeti.dihedralRotations 9 := by
  cases g with
  | r i => exact TauCeti.r_mem_dihedralRotations i
  | sr i =>
      exfalso
      have hdvd : orderOf (DihedralGroup.sr i) ∣ 9 := orderOf_dvd_of_pow_eq_one h
      rw [DihedralGroup.orderOf_sr] at hdvd
      omega

theorem eq_one_of_dihedral_eighteen {K : Subgroup X} [K.Normal] (hKi : K.index = 3)
    (P : Sylow 3 X) (hQc : IsCyclic ↥((P : Subgroup X) ⊓ K))
    (hQ9 : Nat.card ↥((P : Subgroup X) ⊓ K) = 9)
    (hD : Nonempty (↥(K ⊓ normalizer ((((P : Subgroup X) ⊓ K : Subgroup X)) : Set X)) ≃*
      DihedralGroup 9))
    (hP27 : Nat.card ↥(P : Subgroup X) = 27)
    (hPnab : ¬ ∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), a * b = b * a)
    {x : X} (hxP : x ∈ (P : Subgroup X))
    (hx : ∀ n ∈ normalizer ((P : Subgroup X) : Set X), x * n = n * x) : x = 1 := by
  classical
  let Q : Subgroup X := (P : Subgroup X) ⊓ K
  let N : Subgroup X := Subgroup.normalizer (Q : Set X)
  let Γ : Subgroup X := K ⊓ N
  have hQ9' : Nat.card ↥Q = 9 := hQ9
  have hQc' : IsCyclic ↥Q := hQc
  have hQP : Q ≤ (P : Subgroup X) := inf_le_left
  have hQK : Q ≤ K := inf_le_right
  have hxQ : x ∈ Q := by
    by_contra hxQ
    have hle : Q ⊔ Subgroup.zpowers x ≤ (P : Subgroup X) :=
      sup_le hQP (Subgroup.zpowers_le.mpr hxP)
    have hltQ : Q < Q ⊔ Subgroup.zpowers x := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro h
      exact hxQ (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
    have hcard_lt : Nat.card ↥Q < Nat.card ↥(Q ⊔ Subgroup.zpowers x) :=
      Subgroup.card_lt_of_lt hltQ
    have hdvd : Nat.card ↥(Q ⊔ Subgroup.zpowers x) ∣ 27 := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [hP27] at h
    have hdvd' : Nat.card ↥(Q ⊔ Subgroup.zpowers x) ∣ 3 ^ 3 := by
      simpa using hdvd
    obtain ⟨k, hk_le, hk_eq⟩ :=
      (Nat.dvd_prime_pow (p := 3) (m := 3) Nat.prime_three).mp hdvd'
    have hk : k = 3 := by
      rw [hQ9', hk_eq] at hcard_lt
      have hk_ge : 3 ≤ k := by
        by_contra h
        have hk2 : k ≤ 2 := by omega
        have hle_pow : 3 ^ k ≤ 3 ^ 2 :=
          (pow_right_monotone (a := 3) (by norm_num : (1 : ℕ) ≤ 3)) hk2
        norm_num at hle_pow
        omega
      omega
    have hcard : Nat.card ↥(Q ⊔ Subgroup.zpowers x) = 27 := by
      rw [hk_eq, hk]
      norm_num
    have hsup_eq : Q ⊔ Subgroup.zpowers x = (P : Subgroup X) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hP27])
    have hQab : IsMulCommutative ↥Q := hQc'.isMulCommutative
    have hxQ_comm : x ∈ Subgroup.centralizer (Q : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (hx q (Subgroup.le_normalizer (hQP hq))).symm
    have hzpQ : Subgroup.zpowers x ≤ Subgroup.centralizer (Q : Set X) :=
      Subgroup.zpowers_le.mpr hxQ_comm
    have hQzp : Q ≤ Subgroup.centralizer (Subgroup.zpowers x : Set X) :=
      Subgroup.le_centralizer_iff.mpr hzpQ
    have hcomm : ∀ a ∈ Q, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp (hQzp ha) b hb).symm
    have hsup_ab : IsMulCommutative ↥(Q ⊔ Subgroup.zpowers x) :=
      CFSG.GroupTheory.isMulCommutative_sup_of_elementwise_commute hcomm hQab
        (Subgroup.zpowers_isMulCommutative x)
    rw [hsup_eq] at hsup_ab
    exact hPnab fun a ha b hb =>
      congrArg Subtype.val (hsup_ab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨φ⟩ : Nonempty (↥Γ ≃* DihedralGroup 9) := hD
  have hQΓ : Q ≤ Γ := fun q hq => ⟨hQK hq, Subgroup.le_normalizer hq⟩
  let sΓ : ↥Γ := φ.symm (DihedralGroup.sr 0)
  let s : X := sΓ
  have hsΓ : s ∈ Γ := sΓ.2
  have hsN : s ∈ N := hsΓ.2
  have hφs : φ ⟨s, hsΓ⟩ = DihedralGroup.sr 0 := by
    simp [s, sΓ]
  have hsr_not : φ ⟨s, hsΓ⟩ ∉ TauCeti.dihedralRotations 9 := by
    rw [hφs]
    exact TauCeti.sr_notMem_dihedralRotations (0 : ZMod 9)
  have hq9 : ∀ q ∈ Q, q ^ 9 = 1 := by
    intro q hq
    have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨q, hq⟩ : ↥Q)))
    rwa [hQ9'] at h
  have hrot : ∀ q (hq : q ∈ Q), φ ⟨q, hQΓ hq⟩ ∈ TauCeti.dihedralRotations 9 := by
    intro q hq
    apply mem_dihedralRotations_of_pow_nine
    rw [← map_pow]
    have hq9Γ : (⟨q, hQΓ hq⟩ : ↥Γ) ^ 9 = 1 := Subtype.ext (by simpa using hq9 q hq)
    rw [hq9Γ, map_one]
  have hinv : ∀ q ∈ Q, s * q * s⁻¹ = q⁻¹ := by
    intro q hq
    have hconj := TauCeti.conj_eq_inv_of_notMem_dihedralRotations hsr_not (hrot q hq)
    have hconjΓ : sΓ * ⟨q, hQΓ hq⟩ * sΓ⁻¹ = (⟨q, hQΓ hq⟩ : ↥Γ)⁻¹ := by
      apply φ.injective
      simpa [s, sΓ, map_mul, map_inv] using hconj
    simpa [s, sΓ] using congrArg Subtype.val hconjΓ
  have hQleP : Q ≤ (P : Subgroup X) := hQP
  have hQsubEq : Q.subgroupOf (P : Subgroup X) = K.subgroupOf (P : Subgroup X) := by
    ext q
    simp [Q, Subgroup.mem_subgroupOf, and_comm]
  have hQnormP : (Q.subgroupOf (P : Subgroup X)).Normal := by
    rw [hQsubEq]
    exact Subgroup.normal_subgroupOf (H := (P : Subgroup X)) (N := K)
  have hPNQ : (P : Subgroup X) ≤ N :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQleP).mp hQnormP
  have hPK : ¬ (P : Subgroup X) ≤ K := by
    intro h
    have hQeq : Q = (P : Subgroup X) := by
      show (P : Subgroup X) ⊓ K = (P : Subgroup X)
      exact inf_eq_left.mpr h
    have hcard : Nat.card ↥Q = 27 := by rw [hQeq]; exact hP27
    omega
  have hcoat : IsCoatom K := Subgroup.isCoatom_of_index_prime (by rw [hKi]; exact Nat.prime_three)
  have hsupKP : K ⊔ (P : Subgroup X) = ⊤ := by
    have hne : K ⊔ (P : Subgroup X) ≠ K := by
      intro h
      exact hPK (le_sup_right.trans h.le)
    exact (hcoat.ne_iff_eq_top le_sup_left).mp hne
  have hsupKN : K ⊔ N = ⊤ := by
    have hle : K ⊔ (P : Subgroup X) ≤ K ⊔ N := sup_le_sup_left hPNQ K
    exact top_le_iff.mp (hsupKP ▸ hle)
  have hNKnormal : N ≤ Subgroup.normalizer (K : Set X) := Subgroup.le_normalizer_of_normal
  have hΓN : Γ ≤ N := inf_le_right
  have hΓcard : Nat.card ↥Γ = 18 := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  have hrel : Γ.relIndex N = 3 := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := N) (K := K) hNKnormal).2
    rw [sup_comm N K, hsupKN, Subgroup.relIndex_top_right, hKi, inf_comm] at h
    exact h.symm
  have hNcard : Nat.card ↥N = 54 := by
    have h := Subgroup.relIndex_mul_card (H := Γ) (K := N)
    rw [inf_eq_left.mpr hΓN, hrel, hΓcard] at h
    norm_num at h
    exact h.symm
  have hPnorm : (P.subgroupOf N).Normal := by
    apply Subgroup.normal_of_index_eq_two
    have h := Subgroup.relIndex_mul_card (H := (P : Subgroup X)) (K := N)
    rw [inf_eq_left.mpr hPNQ, hP27, hNcard] at h
    have hrelP : (P : Subgroup X).relIndex N = 2 := by omega
    simpa [Subgroup.relIndex] using hrelP
  have hNP : N ≤ Subgroup.normalizer ((P : Subgroup X) : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPNQ).mp hPnorm
  have hsNP : s ∈ Subgroup.normalizer ((P : Subgroup X) : Set X) := hNP hsN
  have hxs : x * s = s * x := hx s hsNP
  have hx_eq_inv : x = x⁻¹ := by
    have h1 : s * x * s⁻¹ = x⁻¹ := hinv x hxQ
    have h2 : s * x * s⁻¹ = x := by
      rw [← hxs]
      group
    exact h2.symm.trans h1
  have hx2 : x ^ 2 = 1 := by
    have h : x * x = x * x⁻¹ := congrArg (fun y => x * y) hx_eq_inv
    rw [mul_inv_cancel] at h
    simpa [pow_two] using h
  have hx9 : x ^ 9 = 1 := hq9 x hxQ
  have h1 : x ^ Nat.gcd 2 9 = 1 :=
    (pow_gcd_eq_one (a := x) (m := 2) (n := 9)).2 ⟨hx2, hx9⟩
  rw [show Nat.gcd 2 9 = 1 by norm_num, pow_one] at h1
  exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ
