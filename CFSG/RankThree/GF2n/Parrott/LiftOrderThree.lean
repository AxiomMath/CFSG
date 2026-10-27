module

public import CFSG.RankThree.GF2n.Parrott.LocalData
public import CFSG.GroupTheory.CentralizerQuotientCard
public import CFSG.RankThree.GF2n.Parrott.PSp43Model
public import Certificates.Certificate946005
public import Certificates.Certificate2012

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

noncomputable def lift3 (x : QA45.originalSubgroup) (hx : orderOf x = 3) : ↥(H z) :=
  let y := lift D x
  let k := orderOf ((y : ↥(H z)) ^ 3)
  let z0 := y ^ k
  if qH D z0 = x then z0 else z0⁻¹

theorem isPGroup_O2_J : IsPGroup 2 (J z) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥(H z))).map (H z).subtype

theorem isPGroup_J_subgroupOf : IsPGroup 2 ((J z).subgroupOf (H z)) :=
  (isPGroup_O2_J (z := z)).of_equiv
    (Subgroup.subgroupOfEquivOfLe (J_le_H (z := z))).symm

theorem coprime_three_card_J : Nat.Coprime 3 (Nat.card (J z)) := by
  obtain ⟨n, hn⟩ := (isPGroup_O2_J (z := z)).exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

theorem coprime_three_card_J_subgroupOf :
    Nat.Coprime 3 (Nat.card ((J z).subgroupOf (H z))) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (J_le_H (z := z))).toEquiv]
  exact coprime_three_card_J (z := z)

theorem qH_lift3 (x : QA45.originalSubgroup) (hx : orderOf x = 3) :
    qH D (lift3 D x hx) = x := by
  classical
  unfold lift3
  dsimp only
  set y : ↥(H z) := lift D x with hy
  set k : ℕ := orderOf (y ^ 3) with hk
  set z0 : ↥(H z) := y ^ k with hz0
  have hqy : qH D y = x := by rw [hy, qH_lift]
  have hq0 : qH D z0 = x ^ k := by rw [hz0, map_pow, hqy]
  have h3dvd : 3 ∣ orderOf y := by
    have h := orderOf_map_dvd (qH D) y
    rwa [hqy, hx] at h
  have hk_eq : k = orderOf y / 3 := by
    rw [hk, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) h3dvd]
  have hy_ne0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  have hz0ord : orderOf z0 = 3 := by
    rw [hz0, hk_eq]
    exact orderOf_pow_orderOf_div (x := y) (n := 3) hy_ne0 h3dvd
  have hz0_not_mem : z0 ∉ (J z).subgroupOf (H z) := by
    intro hz0J
    have hJ2 : IsPGroup 2 ((J z).subgroupOf (H z)) := isPGroup_J_subgroupOf (z := z)
    have hne : (⟨z0, hz0J⟩ : ↥((J z).subgroupOf (H z))) ≠ 1 := by
      intro h
      have hz0one : z0 = 1 := by simpa using congrArg Subtype.val h
      rw [hz0one] at hz0ord
      simp at hz0ord
    have h2dvd := hJ2.dvd_orderOf hne
    rw [Subgroup.orderOf_mk, hz0ord] at h2dvd
    exact (by norm_num : ¬ (2 ∣ 3)) h2dvd
  have hq0_ne : qH D z0 ≠ 1 := by
    intro h
    exact hz0_not_mem ((J_mem_iff D z0).mpr h)
  have hxk_ne : x ^ k ≠ 1 := by
    intro h
    exact hq0_ne (by rw [hq0, h])
  have hkmod : k % 3 = 1 ∨ k % 3 = 2 := by
    have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hne : k % 3 ≠ 0 := by
      intro h0
      apply hxk_ne
      have hmod : x ^ k = x ^ (k % 3) := by
        rw [← pow_mod_orderOf x k, hx]
      rw [hmod, h0, pow_zero]
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exact absurd h0 hne
    · exact Or.inl h1
    · exact Or.inr h2
  have hxkcases : x ^ k = x ∨ x ^ k = x ^ 2 := by
    have hmod : x ^ k = x ^ (k % 3) := by
      rw [← pow_mod_orderOf x k, hx]
    rcases hkmod with h | h
    · left
      rw [hmod, h, pow_one]
    · right
      rw [hmod, h]
  have hqcases : qH D z0 = x ∨ qH D z0 = x ^ 2 := by
    rcases hxkcases with h | h
    · exact Or.inl (by rw [hq0, h])
    · exact Or.inr (by rw [hq0, h])
  split_ifs with h
  · exact h
  · have hq2 : qH D z0 = x ^ 2 := by
      rcases hqcases with hq | hq
      · exact absurd hq h
      · exact hq
    have hx2inv : (x ^ 2)⁻¹ = x := by
      apply inv_eq_of_mul_eq_one_left
      have hx3 : x ^ 3 = 1 := by rw [← hx, pow_orderOf_eq_one]
      simpa [pow_succ'] using hx3
    rw [map_inv, hq2]
    exact hx2inv

theorem orderOf_lift3 (x : QA45.originalSubgroup) (hx : orderOf x = 3) :
    orderOf (lift3 D x hx) = 3 := by
  classical
  unfold lift3
  dsimp only
  set y : ↥(H z) := lift D x with hy
  set k : ℕ := orderOf (y ^ 3) with hk
  set z0 : ↥(H z) := y ^ k with hz0
  have hqy : qH D y = x := by rw [hy, qH_lift]
  have h3dvd : 3 ∣ orderOf y := by
    have h := orderOf_map_dvd (qH D) y
    rwa [hqy, hx] at h
  have hk_eq : k = orderOf y / 3 := by
    rw [hk, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) h3dvd]
  have hy_ne0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  have hz0ord : orderOf z0 = 3 := by
    rw [hz0, hk_eq]
    exact orderOf_pow_orderOf_div (x := y) (n := 3) hy_ne0 h3dvd
  split_ifs with h
  · exact hz0ord
  · rw [orderOf_inv, hz0ord]

theorem card_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    Nat.card (Subgroup.centralizer ({a} : Set A)) =
      Nat.card (Subgroup.centralizer ({(e a)} : Set B)) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv e.toEquiv ?_
  intro x
  change x ∈ Subgroup.centralizer ({a} : Set A) ↔
    e x ∈ Subgroup.centralizer ({(e a)} : Set B)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc e x * e a = e (x * a) := by rw [map_mul]
      _ = e (a * x) := by rw [h]
      _ = e a * e x := by rw [map_mul]
  · intro h
    apply e.injective
    calc e (x * a) = e x * e a := by rw [map_mul]
      _ = e a * e x := h
      _ = e (a * x) := by rw [map_mul]

theorem ker_qH : (qH D).ker = (J z).subgroupOf (H z) := by
  ext x
  rw [MonoidHom.mem_ker, J_mem_iff D]

noncomputable def quotientEquivQA45 :
    (↥(H z) ⧸ (J z).subgroupOf (H z)) ≃* QA45.originalSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq (ker_qH D).symm).trans
    (QuotientGroup.quotientKerEquivOfRightInverse (φ := qH D) (lift D) (qH_lift D))

theorem quotientEquivQA45_coe (a : ↥(H z)) :
    quotientEquivQA45 D (a : ↥(H z) ⧸ (J z).subgroupOf (H z)) = qH D a := by
  change quotientEquivQA45 D (QuotientGroup.mk a) = qH D a
  unfold quotientEquivQA45
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk]

theorem card_centralizer_quotient_eq (a : ↥(H z)) :
    Nat.card (Subgroup.centralizer
        ({(a : ↥(H z) ⧸ (J z).subgroupOf (H z))} :
          Set (↥(H z) ⧸ (J z).subgroupOf (H z)))) =
      Nat.card (Subgroup.centralizer ({qH D a} : Set QA45.originalSubgroup)) := by
  have hq : quotientEquivQA45 D (a : ↥(H z) ⧸ (J z).subgroupOf (H z)) = qH D a :=
    quotientEquivQA45_coe D a
  rw [← hq]
  exact card_centralizer_mulEquiv (quotientEquivQA45 D)
    (a : ↥(H z) ⧸ (J z).subgroupOf (H z))

theorem card_centralizer_QA45_eq_filter (a : Equiv.Perm (Fin 45))
    (ha : a ∈ QA45.originalSubgroup) :
    Nat.card (Subgroup.centralizer ({⟨a, ha⟩} : Set QA45.originalSubgroup)) =
      ((elemsT QA45).filter (fun g => g * a = a * g)).length := by
  have hcf := card_filter QA45 QA45_ok
    (p := fun g : Equiv.Perm (Fin 45) => g * a = a * g)
  rw [← hcf]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight ?_
  intro g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    simpa using congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem orderOf_sigma1_subtype :
    orderOf (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    simpa using sigma1_cube
  · intro h
    exact sigma1_ne_one (by simpa using congrArg Subtype.val h)

theorem orderOf_sigma2_subtype :
    orderOf (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    simpa using sigma2_cube
  · intro h
    exact sigma2_ne_one (by simpa using congrArg Subtype.val h)

noncomputable def sigma1H3 : ↥(H z) :=
  lift3 D ⟨sigma1, sigma1_mem_A⟩ orderOf_sigma1_subtype

noncomputable def sigma2H3 : ↥(H z) :=
  lift3 D ⟨sigma2, sigma2_mem_A⟩ orderOf_sigma2_subtype

@[simp] theorem qH_sigma1H3 : qH D (sigma1H3 D) = ⟨sigma1, sigma1_mem_A⟩ :=
  qH_lift3 D _ _

@[simp] theorem qH_sigma2H3 : qH D (sigma2H3 D) = ⟨sigma2, sigma2_mem_A⟩ :=
  qH_lift3 D _ _

theorem card_centralizer_sigma1_QA45 :
    Nat.card (Subgroup.centralizer
        ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup)) = 648 := by
  rw [card_centralizer_QA45_eq_filter sigma1 sigma1_mem_A]
  exact Certificates.certificate946005.centralizer_sigma1

end CFSG.RankThree.GF2n.Parrott
