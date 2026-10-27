module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

structure PInvol (p : ℕ) (Q : Subgroup G) (u : G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  exp : ∀ x ∈ Q, x ^ p = 1
  class_two : ∀ x ∈ Q, ∀ y ∈ Q, ∀ z ∈ Q, ⁅⁅x, y⁆, z⁆ = 1
  sq_eq_one : u * u = 1
  mem_normalizer : u ∈ Subgroup.normalizer (Q : Set G)
  le_commutator : Q ≤ ⁅Q, Subgroup.zpowers u⁆

@[expose] def InvertedSmall (p : ℕ) (Q : Subgroup G) (u : G) : Prop :=
  ∀ S : Subgroup G, S ≤ Q → (∀ s ∈ S, u * s * u⁻¹ = s⁻¹) → Nat.card S ≤ p

@[expose] def CentralSmall (p : ℕ) (Q : Subgroup G) (u : G) : Prop :=
  ∀ S : Subgroup G, S ≤ Q → (∀ s ∈ S, ∀ x ∈ Q, s * x = x * s) → (∀ s ∈ S, u * s = s * u) →
    Nat.card S ≤ p

private lemma s763G_alpha_mem {p : ℕ} {Q : Subgroup G} {u : G} (h : PInvol p Q u) {x : G}
    (hx : x ∈ Q) : u * x * u⁻¹ ∈ Q := by
  have hmem := h.mem_normalizer
  rw [Subgroup.mem_set_normalizer_iff] at hmem
  exact (hmem x).mp hx

private lemma s763G_zpowers_u_eq {u : G} (hu : u * u = 1) {v : G}
    (hv : v ∈ Subgroup.zpowers u) : v = 1 ∨ v = u := by
  let K : Subgroup G :=
    { carrier := {x : G | x = 1 ∨ x = u}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro a b ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
        · exact Or.inl hu
      inv_mem' := by
        intro a ha
        rcases ha with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (inv_eq_of_mul_eq_one_right hu) }
  exact (Subgroup.zpowers_le (g := u) (H := K)).mpr (Or.inr rfl) hv

private lemma s763G_commutator_mem_Q {p : ℕ} {Q : Subgroup G} {u : G} (h : PInvol p Q u) {z : G}
    (hz : z ∈ Q) : ⁅z, u⁆ ∈ Q := by
  have hzinv : z⁻¹ ∈ Q := Q.inv_mem hz
  have huz : u * z⁻¹ * u⁻¹ ∈ Q := s763G_alpha_mem h hzinv
  have heq : ⁅z, u⁆ = z * (u * z⁻¹ * u⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact Q.mul_mem hz huz

private lemma s763G_u_conj_commutator {p : ℕ} {Q : Subgroup G} {u : G} (h : PInvol p Q u)
    {z : G} (_hz : z ∈ Q) : u * ⁅z, u⁆ * u⁻¹ = ⁅z, u⁆⁻¹ := by
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right h.sq_eq_one
  have hexp : (z * u * z⁻¹ * u⁻¹)⁻¹ = u * z * u⁻¹ * z⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv]
    group
  rw [commutatorElement_def, hexp, hu]
  rw [show u * (z * u * z⁻¹ * u) * u = (u * z * u * z⁻¹) * (u * u) by group]
  rw [h.sq_eq_one, mul_one]

private lemma s763G_commutator_central {p : ℕ} {Q : Subgroup G} {u : G} (h : PInvol p Q u) :
    ⁅Q, Q⁆ ≤ Subgroup.centralizer (Q : Set G) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [← commutatorElement_eq_one_iff_mul_comm]
  rw [← commutatorElement_inv, h.class_two x hx y hy z hz, inv_one]

private lemma s763G_commutator_mul_mem_commutator_central {Q : Subgroup G}
    (hD : ⁅Q, Q⁆ ≤ Subgroup.centralizer (Q : Set G)) {a b : G}
    (ha : a ∈ ⁅Q, Q⁆) (hb : b ∈ ⁅Q, Q⁆) {p q : G} (hp : p ∈ Q) (hq : q ∈ Q) :
    ⁅a * p, b * q⁆ = ⁅p, q⁆ := by
  have haQ : a ∈ Q := Subgroup.commutator_le_self Q ha
  have hbQ : b ∈ Q := Subgroup.commutator_le_self Q hb
  have hbqQ : b * q ∈ Q := Q.mul_mem hbQ hq
  have hpqD : ⁅p, q⁆ ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator hp hq
  have hpqQ : ⁅p, q⁆ ∈ Q := Subgroup.commutator_le_self Q hpqD
  have hpbqQ : ⁅p, b * q⁆ ∈ Q :=
    Subgroup.commutator_le_self Q (Subgroup.commutator_mem_commutator hp hbqQ)
  have habq : ⁅a, b * q⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hD ha) (b * q) hbqQ).symm
  have hconja : a * ⁅p, b * q⁆ * a⁻¹ = ⁅p, b * q⁆ := by
    have hh := Subgroup.mem_centralizer_iff.mp (hD ha) ⁅p, b * q⁆ hpbqQ
    rw [← hh, mul_assoc, mul_inv_cancel, mul_one]
  have hpb : ⁅p, b⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hD hb) p hp
  have hconjb : b * ⁅p, q⁆ * b⁻¹ = ⁅p, q⁆ := by
    have hh := Subgroup.mem_centralizer_iff.mp (hD hb) ⁅p, q⁆ hpqQ
    rw [← hh, mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_mul_left_eq_conj_mul, habq, mul_one, hconja,
    commutatorElement_mul_right_eq_mul_conj, hpb, one_mul, hconjb]

theorem PInvol.mul_inv_mul_mem_commutator {p : ℕ} {Q : Subgroup G} {u : G} (h : PInvol p Q u)
    {x : G} (hx : x ∈ Q) : u * x * u⁻¹ * x ∈ ⁅Q, Q⁆ := by
  let T : Subgroup G :=
    { carrier := {y : G | y ∈ Q ∧ u * y * u⁻¹ * y ∈ ⁅Q, Q⁆}
      one_mem' := by
        refine ⟨Q.one_mem, ?_⟩
        have hone : u * 1 * u⁻¹ * 1 = 1 := by group
        rw [hone]
        exact Subgroup.one_mem _
      mul_mem' := by
        intro y z hy hz
        obtain ⟨hyQ, hyD⟩ := hy
        obtain ⟨hzQ, hzD⟩ := hz
        refine ⟨Q.mul_mem hyQ hzQ, ?_⟩
        have haQ : u * y * u⁻¹ ∈ Q := s763G_alpha_mem h hyQ
        have hbQ : u * z * u⁻¹ ∈ Q := s763G_alpha_mem h hzQ
        have hconj : (u * y * u⁻¹) * ⁅u * z * u⁻¹, y⁆ * (u * y * u⁻¹)⁻¹ ∈ ⁅Q, Q⁆ := by
          have hnorm := Subgroup.normalizer_commutator_ge_left Q Q haQ
          rw [Subgroup.mem_set_normalizer_iff] at hnorm
          exact (hnorm ⁅u * z * u⁻¹, y⁆).mp (Subgroup.commutator_mem_commutator hbQ hyQ)
        have hprod : (u * y * u⁻¹) * ⁅u * z * u⁻¹, y⁆ * (u * y * u⁻¹)⁻¹
            * (u * y * u⁻¹ * y) * (u * z * u⁻¹ * z) ∈ ⁅Q, Q⁆ :=
          mul_mem (mul_mem hconj hyD) hzD
        convert hprod using 1
        simp only [commutatorElement_def]
        group
      inv_mem' := by
        intro y hy
        obtain ⟨hyQ, hyD⟩ := hy
        refine ⟨Q.inv_mem hyQ, ?_⟩
        have hconj : y * (u * y * u⁻¹ * y) * y⁻¹ ∈ ⁅Q, Q⁆ := by
          have hnorm := Subgroup.normalizer_commutator_ge_left Q Q hyQ
          rw [Subgroup.mem_set_normalizer_iff] at hnorm
          exact (hnorm (u * y * u⁻¹ * y)).mp hyD
        have hyay : y * (u * y * u⁻¹) ∈ ⁅Q, Q⁆ := by
          convert hconj using 1
          group
        have hneg : (y * (u * y * u⁻¹))⁻¹ ∈ ⁅Q, Q⁆ := Subgroup.inv_mem _ hyay
        convert hneg using 1
        group }
  have hgen : ⁅Q, Subgroup.zpowers u⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro z hz v hv
    rcases s763G_zpowers_u_eq h.sq_eq_one hv with rfl | rfl
    · rw [commutatorElement_one_right]
      exact T.one_mem
    · refine ⟨s763G_commutator_mem_Q h hz, ?_⟩
      rw [s763G_u_conj_commutator h hz, inv_mul_cancel]
      exact Subgroup.one_mem _
  exact (hgen (h.le_commutator hx)).2

theorem PInvol.mem_commutator_of_commute {p : ℕ} {Q : Subgroup G} {u : G} (h : PInvol p Q u)
    {x : G} (hx : x ∈ Q) (hc : u * x = x * u) : x ∈ ⁅Q, Q⁆ := by
  have hcx : u * x * u⁻¹ = x := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hxx : x * x ∈ ⁅Q, Q⁆ := by
    have h1 := PInvol.mul_inv_mul_mem_commutator h hx
    simpa [hcx] using h1
  have hp1 : 2 * ((p + 1) / 2) = p + 1 :=
    Nat.two_mul_div_two_of_even (h.prime.odd_of_ne_two h.odd).add_one
  have hxeq : x = (x * x) ^ ((p + 1) / 2) := by
    calc
      x = x ^ (p + 1) := by rw [pow_succ, h.exp x hx, one_mul]
      _ = x ^ (2 * ((p + 1) / 2)) := by rw [hp1]
      _ = (x * x) ^ ((p + 1) / 2) := by
            rw [← pow_two x, ← pow_mul x 2 ((p + 1) / 2)]
  exact (by simpa [← hxeq] using pow_mem hxx ((p + 1) / 2))

theorem PInvol.commute_of_mem_commutator {p : ℕ} {Q : Subgroup G} {u : G} (h : PInvol p Q u)
    {x : G} (hx : x ∈ ⁅Q, Q⁆) : u * x = x * u := by
  have hD : ⁅Q, Q⁆ ≤ Subgroup.centralizer (Q : Set G) := s763G_commutator_central h
  have hDu : ⁅Q, Q⁆ ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.commutator_le]
    intro y hy z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcD : ⁅y, z⁆ ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator hy hz
    have hcy : u * ⁅y, z⁆ * u⁻¹ = ⁅y, z⁆ := by
      calc
        u * ⁅y, z⁆ * u⁻¹ = ⁅u * y * u⁻¹, u * z * u⁻¹⁆ :=
          conjugate_commutatorElement (g₁ := y) (g₂ := z) (g₃ := u)
        _ = ⁅(u * y * u⁻¹ * y) * y⁻¹, (u * z * u⁻¹ * z) * z⁻¹⁆ := by
              simp only [commutatorElement_def]
              group
        _ = ⁅y⁻¹, z⁻¹⁆ := s763G_commutator_mul_mem_commutator_central hD
              (PInvol.mul_inv_mul_mem_commutator h hy)
              (PInvol.mul_inv_mul_mem_commutator h hz) (Q.inv_mem hy) (Q.inv_mem hz)
        _ = ⁅y, z⁆ := by
              have hid : ⁅y⁻¹, z⁻¹⁆ = z⁻¹ * (y⁻¹ * ⁅y, z⁆ * y) * z := by
                simp only [commutatorElement_def]
                group
              rw [hid]
              have hyc : y⁻¹ * ⁅y, z⁆ * y = ⁅y, z⁆ := by
                have hh := Subgroup.mem_centralizer_iff.mp (hD hcD) y⁻¹ (Q.inv_mem hy)
                rw [hh, mul_assoc, inv_mul_cancel, mul_one]
              have hzc : z⁻¹ * ⁅y, z⁆ * z = ⁅y, z⁆ := by
                have hh := Subgroup.mem_centralizer_iff.mp (hD hcD) z⁻¹ (Q.inv_mem hz)
                rw [hh, mul_assoc, inv_mul_cancel, mul_one]
              rw [hyc, hzc]
    have hucy : u * ⁅y, z⁆ = ⁅y, z⁆ * u := by
      calc
        u * ⁅y, z⁆ = (u * ⁅y, z⁆ * u⁻¹) * u := by group
        _ = ⁅y, z⁆ * u := by rw [hcy]
    exact hucy.symm
  have hxu : x ∈ Subgroup.centralizer ({u} : Set G) := hDu hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hxu
  exact hxu.symm

theorem PInvol.card_le_of_commutative [Finite G] {p : ℕ} {Q : Subgroup G} {u : G}
    (h : PInvol p Q u) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ = 1) (h1 : InvertedSmall p Q u) :
    Nat.card Q ≤ p := by
  have hbot : ⁅Q, Q⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot]
    exact hQ x hx y hy
  apply h1 Q le_rfl
  intro x hx
  have h1x : u * x * u⁻¹ * x ∈ ⁅Q, Q⁆ := PInvol.mul_inv_mul_mem_commutator h hx
  rw [hbot, Subgroup.mem_bot] at h1x
  exact mul_eq_one_iff_eq_inv.mp h1x

end CFSG.LocalAnalysis.WeakClosure81
