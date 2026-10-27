module

public import CFSG.RankThree.Native.F5FourDimFormSpace
public import CFSG.Monster.B.Pinned.Primes.Extraspecial
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.Native.FiveLocal

open Subgroup CFSG.Monster.B.Pinned
open scoped Matrix

variable {G : Type*} [Group G]

abbrev Q (q : Fin 4 → G) : Subgroup G := closure (Set.range q)

@[expose] def K (x h : G) (q : Fin 4 → G) : Subgroup G := closure ((Q q : Set G) ∪ {x, h})

@[expose] def ZQ (q : Fin 4 → G) : Subgroup G := (center (Q q)).map (Q q).subtype

@[expose] def H0 (x h : G) (q : Fin 4 → G) : Subgroup G := K x h q ⊓ centralizer (ZQ q : Set G)

@[expose] def P (x : G) (q : Fin 4 → G) : Subgroup G := Q q ⊔ zpowers x

@[expose] noncomputable def A (q : Fin 4 → G) (z g : G) : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  CommData.actMat 5 q z f5M g

@[expose] noncomputable def crd (q : Fin 4 → G) (z g : G) : Fin 4 → ZMod 5 := coord 5 q z f5M g

@[expose] def xc : Fin 4 → ℕ := ![0, 0, 0, 1]

@[expose] def hc : Fin 4 → ℕ := ![0, 1, 2, 2]

structure Rel (x h : G) (q : Fin 4 → G) (z : G) : Prop where
  commData : CommData 5 q z f5M
  z_eq : bcomm (q 0) (q 1) = z
  orderOf_x : orderOf x = 5
  conj_x : ∀ i, x⁻¹ * q i * x = (List.ofFn fun j => q j ^ (f5X i j).val).prod * z ^ xc i
  conj_xz : x⁻¹ * z * x = z
  conj_h : ∀ i, h⁻¹ * q i * h = (List.ofFn fun j => q j ^ (f5H i j).val).prod * z ^ hc i
  conj_hz : h⁻¹ * z * h = z ^ 2

section Generic

variable {x h : G} {q : Fin 4 → G}

theorem q_mem (i : Fin 4) : q i ∈ Q q := subset_closure ⟨i, rfl⟩

theorem Q_le_K : Q q ≤ K x h q := fun _ hg => subset_closure (Or.inl hg)

theorem x_mem_K : x ∈ K x h q := subset_closure (Or.inr (Or.inl rfl))

theorem h_mem_K : h ∈ K x h q := subset_closure (Or.inr (Or.inr rfl))

theorem H0_le_K : H0 x h q ≤ K x h q := inf_le_left

theorem mul_pow_class_two {a b c : G}
    (hc : b * a = a * b * c) (hca : Commute c a) (hcb : Commute c b) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n * c ^ n.choose 2 := by
  have hbk : ∀ k : ℕ, b ^ k * a = a * b ^ k * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc b ^ (k + 1) * a = b * (b ^ k * a) := by rw [pow_succ', mul_assoc]
        _ = b * (a * b ^ k * c ^ k) := by rw [ih]
        _ = (b * a) * b ^ k * c ^ k := by group
        _ = a * b * c * b ^ k * c ^ k := by rw [hc]
        _ = a * b * (c * b ^ k) * c ^ k := by group
        _ = a * b * (b ^ k * c) * c ^ k := by rw [(hcb.pow_right k).eq]
        _ = a * b ^ (k + 1) * c ^ (k + 1) := by rw [pow_succ' b k, pow_succ' c k]; group
  induction n with
  | zero => simp
  | succ n ih =>
    have hT : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    have e1 : c ^ n.choose 2 * a = a * c ^ n.choose 2 := (hca.pow_left _).eq
    have e2 : c ^ n.choose 2 * b = b * c ^ n.choose 2 := (hcb.pow_left _).eq
    have e3 : c ^ n * b = b * c ^ n := (hcb.pow_left _).eq
    rw [pow_succ, ih, hT, pow_add c n (n.choose 2)]
    calc a ^ n * b ^ n * c ^ n.choose 2 * (a * b)
        = a ^ n * b ^ n * (c ^ n.choose 2 * a) * b := by group
      _ = a ^ n * (b ^ n * a) * (c ^ n.choose 2 * b) := by rw [e1]; group
      _ = a ^ n * (a * b ^ n * c ^ n) * (b * c ^ n.choose 2) := by rw [hbk, e2]
      _ = a ^ n * a * b ^ n * (c ^ n * b) * c ^ n.choose 2 := by group
      _ = a ^ n * a * b ^ n * (b * c ^ n) * c ^ n.choose 2 := by rw [e3]
      _ = a ^ (n + 1) * b ^ (n + 1) * (c ^ n * c ^ n.choose 2) := by
        rw [pow_succ a n, pow_succ b n]; group

end Generic

namespace Rel

variable {x h z : G} {q : Fin 4 → G} (hR : Rel x h q z)
include hR

theorem z_mem : z ∈ Q q := hR.commData.mem_z

theorem orderOf_z : orderOf z = 5 := hR.commData.orderOf_z

theorem z_pow_five : z ^ 5 = 1 := by rw [← hR.orderOf_z]; exact pow_orderOf_eq_one z

theorem prod_mem (a : Fin 4 → ℕ) (c : ℕ) :
    (List.ofFn fun j => q j ^ a j).prod * z ^ c ∈ Q q := by
  refine mul_mem (list_prod_mem fun g hg => ?_) (pow_mem hR.z_mem _)
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
  exact pow_mem (q_mem j) _

theorem conj_x_mem (i : Fin 4) : x⁻¹ * q i * x ∈ Q q := by
  rw [hR.conj_x i]
  exact hR.prod_mem _ _

theorem conj_h_mem (i : Fin 4) : h⁻¹ * q i * h ∈ Q q := by
  rw [hR.conj_h i]
  exact hR.prod_mem _ _

theorem x_conj_mem_Q : ∀ g ∈ Q q, x⁻¹ * g * x ∈ Q q := fun _ hg =>
  CommData.conj_mem hR.conj_x_mem hg

theorem h_conj_mem_Q : ∀ g ∈ Q q, h⁻¹ * g * h ∈ Q q := fun _ hg =>
  CommData.conj_mem hR.conj_h_mem hg

theorem bcomm_mem {u v : G} (hu : u ∈ Q q) (hv : v ∈ Q q) : bcomm u v ∈ zpowers z :=
  hR.commData.bcomm_mem hu hv

theorem x_not_mem_Q : x ∉ Q q :=
  hR.commData.not_mem_of_conj (i := 0) (j := 2) (by
    rw [hR.conj_x 0]
    simp [List.ofFn_succ, f5X, xc, show (1 : ZMod 5).val = 1 from rfl]) (by decide +kernel)

theorem lg_inv {y : G} (hy : y ∈ zpowers z) : lg 5 z y⁻¹ = -lg 5 z y := by
  have h := lg_mul (p := 5) hR.orderOf_z hy (inv_mem hy)
  rw [mul_inv_cancel, lg_one hR.orderOf_z] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem bcomm_mul_right {u v w : G} (hu : u ∈ Q q) (hv : v ∈ Q q) (hw : w ∈ Q q) :
    bcomm u (v * w) = bcomm u v * bcomm u w := by
  have h1 : bcomm (v * w) u = bcomm v u * bcomm w u := hR.commData.bcomm_mul hv hw hu
  have hcomm : Commute (bcomm u v) (bcomm u w) := by
    obtain ⟨a, ha⟩ := mem_zpowers_iff.1 (hR.bcomm_mem hu hv)
    obtain ⟨b, hb⟩ := mem_zpowers_iff.1 (hR.bcomm_mem hu hw)
    rw [← ha, ← hb]
    exact (Commute.refl z).zpow_zpow a b
  calc bcomm u (v * w) = (bcomm (v * w) u)⁻¹ := bcomm_swap _ _
    _ = (bcomm v u * bcomm w u)⁻¹ := by rw [h1]
    _ = (bcomm w u)⁻¹ * (bcomm v u)⁻¹ := mul_inv_rev _ _
    _ = bcomm u w * bcomm u v := by rw [← bcomm_swap, ← bcomm_swap]
    _ = bcomm u v * bcomm u w := hcomm.eq.symm

theorem bcomm_inv_right {u v : G} (hu : u ∈ Q q) (hv : v ∈ Q q) :
    bcomm u v⁻¹ = (bcomm u v)⁻¹ := by
  have h := hR.bcomm_mul_right hu (inv_mem hv) hv
  rw [inv_mul_cancel, show bcomm u 1 = 1 by simp [bcomm]] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem psi_eq (u : G) : psi 5 q z u = crd q z u ᵥ* f5M := by
  rw [crd, coord, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hR.commData.isUnit_det,
    Matrix.vecMul_one]

theorem lg_bcomm {u v : G} (hu : u ∈ Q q) (hv : v ∈ Q q) :
    lg 5 z (bcomm u v) = crd q z u ⬝ᵥ (f5M *ᵥ crd q z v) := by
  have hpsi := hR.psi_eq u
  unfold crd at hpsi ⊢
  induction hv using closure_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    have h1 : lg 5 z (bcomm u (q j)) = psi 5 q z u j := rfl
    rw [h1, hpsi, hR.commData.coord_q j, Matrix.mulVec_single_one]
    rfl
  | one =>
    rw [show bcomm u 1 = 1 by simp [bcomm], lg_one hR.orderOf_z, hR.commData.coord_one,
      Matrix.mulVec_zero, dotProduct_zero]
  | mul v w hv hw ihv ihw =>
    rw [hR.bcomm_mul_right hu hv hw, lg_mul hR.orderOf_z (hR.bcomm_mem hu hv)
      (hR.bcomm_mem hu hw), ihv, ihw, hR.commData.coord_mul hv hw, Matrix.mulVec_add,
      dotProduct_add]
  | inv v hv ihv =>
    rw [hR.bcomm_inv_right hu hv, hR.lg_inv (hR.bcomm_mem hu hv), ihv,
      hR.commData.coord_inv hv, Matrix.mulVec_neg, dotProduct_neg]
    rfl

theorem pow_five_of_mem {g : G} (hg : g ∈ Q q) : g ^ 5 = 1 := by
  induction hg using closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    exact hR.commData.pow_q i
  | one => exact one_pow 5
  | mul a b ha hb iha ihb =>
    set c := bcomm b a with hcdef
    have hcz : c ∈ zpowers z := hR.bcomm_mem hb ha
    have hc : b * a = a * b * c := by rw [hcdef, bcomm]; group
    have hca : Commute c a := (hR.commData.commute_of_mem ha hcz).symm
    have hcb : Commute c b := (hR.commData.commute_of_mem hb hcz).symm
    have hc5 : c ^ 5 = 1 := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hcz
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hR.z_pow_five,
        one_zpow]
    rw [mul_pow_class_two hc hca hcb, iha, ihb, show (5 : ℕ).choose 2 = 5 * 2 by decide,
      pow_mul, hc5, one_pow, one_mul, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

variable [Finite G]

theorem K_le_normalizer : K x h q ≤ normalizer (Q q : Set G) := by
  rw [K, closure_le]
  rintro g (hg | rfl | rfl)
  · exact le_normalizer hg
  · exact mem_normalizer_of_conj hR.x_conj_mem_Q
  · exact mem_normalizer_of_conj hR.h_conj_mem_Q

theorem conj_mem_of_mem_K {g : G} (hg : g ∈ K x h q) {u : G} (hu : u ∈ Q q) :
    g⁻¹ * u * g ∈ Q q := by
  have := (mem_normalizer_iff.1 (inv_mem (hR.K_le_normalizer hg)) u).1 hu
  rwa [inv_inv] at this

theorem center_Q_eq : center (Q q) = (zpowers z).subgroupOf (Q q) := hR.commData.center_eq

theorem ZQ_eq : ZQ q = zpowers z := by
  rw [ZQ, hR.center_Q_eq, subgroupOf_map_subtype, inf_eq_left.2 (zpowers_le.2 hR.z_mem)]

theorem centralizer_ZQ : centralizer (ZQ q : Set G) = centralizer {z} := by
  rw [hR.ZQ_eq, zpowers_eq_closure, centralizer_closure]

theorem mem_H0 {g : G} : g ∈ H0 x h q ↔ g ∈ K x h q ∧ g * z = z * g := by
  rw [H0, mem_inf, hR.centralizer_ZQ, mem_centralizer_singleton_iff]

theorem Q_le_H0 : Q q ≤ H0 x h q := fun _ hg =>
  hR.mem_H0.2 ⟨Q_le_K hg, (hR.commData.commute_of_mem hg (mem_zpowers z))⟩

theorem x_mem_H0 : x ∈ H0 x h q := by
  refine hR.mem_H0.2 ⟨x_mem_K, ?_⟩
  have e := hR.conj_xz
  calc x * z = x * (x⁻¹ * z * x) := by rw [e]
    _ = z * x := by group

theorem P_le_H0 : P x q ≤ H0 x h q := sup_le hR.Q_le_H0 (zpowers_le.2 hR.x_mem_H0)

theorem P_le_K : P x q ≤ K x h q := hR.P_le_H0.trans H0_le_K

theorem card_Q : Nat.card (Q q) = 5 ^ 5 := hR.commData.card_eq

theorem card_P : Nat.card (P x q) = 5 ^ 6 := by
  rw [P, card_sup_zpowers hR.orderOf_x hR.x_not_mem_Q hR.x_conj_mem_Q, hR.card_Q]
  norm_num

theorem isPGroup_Q : IsPGroup 5 (Q q) := IsPGroup.of_card hR.card_Q

end Rel

end CFSG.RankThree.Native.FiveLocal
