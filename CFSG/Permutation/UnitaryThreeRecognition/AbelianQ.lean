module

public import CFSG.Permutation.UnitaryThreeRecognition.Fixed
public import Mathlib.Data.Rat.Floor

public section

open MulAction

namespace CFSG.UnitaryThreeRecognition

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace AbelianQ

@[expose] def invSub (Q : Subgroup G) (j : G) (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    Subgroup G where
  carrier := {u | u ∈ Q ∧ j * u * j⁻¹ = u⁻¹}
  mul_mem' := by
    rintro x y ⟨hx, hjx⟩ ⟨hy, hjy⟩
    refine ⟨Q.mul_mem hx hy, ?_⟩
    calc j * (x * y) * j⁻¹ = (j * x * j⁻¹) * (j * y * j⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [hjx, hjy]
      _ = (x * y)⁻¹ := by rw [mul_inv_rev]; exact hQab _ (Q.inv_mem hx) _ (Q.inv_mem hy)
  one_mem' := ⟨Q.one_mem, by group⟩
  inv_mem' := by
    rintro x ⟨hx, hjx⟩
    refine ⟨Q.inv_mem hx, ?_⟩
    calc j * x⁻¹ * j⁻¹ = (j * x * j⁻¹)⁻¹ := by group
      _ = x⁻¹⁻¹ := by rw [hjx]

variable {Q : Subgroup G} {j : G} {hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x}

theorem mem_invSub {u : G} : u ∈ invSub Q j hQab ↔ u ∈ Q ∧ j * u * j⁻¹ = u⁻¹ :=
  Iff.rfl

theorem invSub_le : invSub Q j hQab ≤ Q := fun _ hu => hu.1

omit hQab in
theorem pow_half_sq [Finite Q] {h : ℕ} (hh : h * 2 = Nat.card Q + 1) {u : G} (hu : u ∈ Q) :
    (u ^ h) ^ 2 = u := by
  have h2 : u ^ Nat.card Q = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨u, hu⟩ : Q)))
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h
    exact h
  rw [← pow_mul, hh, pow_succ, h2, one_mul]

omit hQab in
theorem eq_one_of_mul_self_eq_one [Finite Q] (hodd : Odd (Nat.card Q)) {u : G} (hu : u ∈ Q)
    (hu2 : u * u = 1) : u = 1 := by
  obtain ⟨h, hh⟩ : ∃ h, h * 2 = Nat.card Q + 1 :=
    ⟨(Nat.card Q + 1) / 2, by obtain ⟨k, hk⟩ := hodd; omega⟩
  calc u = (u ^ h) ^ 2 := (pow_half_sq hh hu).symm
    _ = (u * u) ^ h := by rw [← pow_mul, mul_comm h 2, pow_mul, sq]
    _ = 1 := by rw [hu2, one_pow]

include hQab in
theorem exists_centQ_mul_invSub [Finite Q] (hodd : Odd (Nat.card Q))
    (hjQ : ∀ x ∈ Q, j * x * j⁻¹ ∈ Q) (hj2 : j * j = 1) {u : G} (hu : u ∈ Q) :
    ∃ z ∈ centQ Q j, ∃ v ∈ invSub Q j hQab, u = z * v := by
  obtain ⟨h, hh⟩ : ∃ h, h * 2 = Nat.card Q + 1 :=
    ⟨(Nat.card Q + 1) / 2, by obtain ⟨k, hk⟩ := hodd; omega⟩
  have hu'Q : j * u * j⁻¹ ∈ Q := hjQ u hu
  have hju' : j * (j * u * j⁻¹) * j⁻¹ = u := by
    calc j * (j * u * j⁻¹) * j⁻¹ = (j * j) * u * (j * j)⁻¹ := by group
      _ = u := by rw [hj2]; group
  have hcomm : Commute u (j * u * j⁻¹) := hQab _ hu _ hu'Q
  refine ⟨(u * (j * u * j⁻¹)) ^ h, mem_centQ.mpr ⟨Q.pow_mem (Q.mul_mem hu hu'Q) h, ?_⟩,
    (u * (j * u * j⁻¹)⁻¹) ^ h, ⟨Q.pow_mem (Q.mul_mem hu (Q.inv_mem hu'Q)) h, ?_⟩, ?_⟩
  · have hconj : j * (u * (j * u * j⁻¹)) ^ h * j⁻¹ = (u * (j * u * j⁻¹)) ^ h := by
      rw [← conj_pow]
      congr 1
      calc j * (u * (j * u * j⁻¹)) * j⁻¹ = (j * u * j⁻¹) * (j * (j * u * j⁻¹) * j⁻¹) := by
            group
        _ = (j * u * j⁻¹) * u := by rw [hju']
        _ = u * (j * u * j⁻¹) := hcomm.symm.eq
    calc j * (u * (j * u * j⁻¹)) ^ h = j * (u * (j * u * j⁻¹)) ^ h * j⁻¹ * j := by group
      _ = (u * (j * u * j⁻¹)) ^ h * j := by rw [hconj]
  · rw [← conj_pow, ← inv_pow]
    congr 1
    calc j * (u * (j * u * j⁻¹)⁻¹) * j⁻¹ =
          (j * u * j⁻¹) * (j * (j * u * j⁻¹) * j⁻¹)⁻¹ := by group
      _ = (j * u * j⁻¹) * u⁻¹ := by rw [hju']
      _ = (u * (j * u * j⁻¹)⁻¹)⁻¹ := by group
  · have hc2 : Commute (u * (j * u * j⁻¹)) (u * (j * u * j⁻¹)⁻¹) :=
      ((Commute.refl u).mul_right hcomm.inv_right).mul_left
        (hcomm.symm.mul_right (Commute.refl _).inv_right)
    rw [← hc2.mul_pow]
    have : u * (j * u * j⁻¹) * (u * (j * u * j⁻¹)⁻¹) = u ^ 2 := by
      calc u * (j * u * j⁻¹) * (u * (j * u * j⁻¹)⁻¹) =
            u * ((j * u * j⁻¹) * u) * (j * u * j⁻¹)⁻¹ := by group
        _ = u * (u * (j * u * j⁻¹)) * (j * u * j⁻¹)⁻¹ := by rw [hcomm.eq]
        _ = u ^ 2 := by rw [sq]; group
    rw [this, ← pow_mul, mul_comm 2 h, pow_mul, pow_half_sq hh hu]

theorem eq_one_of_mem_centQ_of_mem_invSub [Finite Q] (hodd : Odd (Nat.card Q)) {u : G}
    (hz : u ∈ centQ Q j) (hv : u ∈ invSub Q j hQab) : u = 1 := by
  obtain ⟨huQ, hju⟩ := mem_centQ.mp hz
  have h1 : j * u * j⁻¹ = u := by rw [hju, mul_inv_cancel_right]
  have h2 : u⁻¹ = u := by rw [← hv.2, h1]
  apply eq_one_of_mul_self_eq_one hodd huQ
  nth_rewrite 1 [← h2]
  exact inv_mul_cancel u

include hQab in
theorem card_eq_card_centQ_mul [Finite Q] (hodd : Odd (Nat.card Q))
    (hjQ : ∀ x ∈ Q, j * x * j⁻¹ ∈ Q) (hj2 : j * j = 1) :
    Nat.card Q = Nat.card (centQ Q j) * Nat.card (invSub Q j hQab) := by
  rw [← Nat.card_prod]
  symm
  apply Nat.card_eq_of_bijective (fun zv : centQ Q j × invSub Q j hQab =>
    (⟨(zv.1 : G) * zv.2, Q.mul_mem (mem_centQ.mp zv.1.2).1 zv.2.2.1⟩ : Q))
  constructor
  · rintro ⟨z, v⟩ ⟨z', v'⟩ h
    have h' : (z : G) * v = z' * v' := congrArg Subtype.val h
    have hzz : (z' : G)⁻¹ * z = v' * (v : G)⁻¹ := by
      calc (z' : G)⁻¹ * z = (z' : G)⁻¹ * (z * v) * (v : G)⁻¹ := by group
        _ = (z' : G)⁻¹ * (z' * v') * (v : G)⁻¹ := by rw [h']
        _ = v' * (v : G)⁻¹ := by group
    have h1 : (z' : G)⁻¹ * z = 1 := by
      apply eq_one_of_mem_centQ_of_mem_invSub (hQab := hQab) hodd
      · exact (centQ Q j).mul_mem ((centQ Q j).inv_mem z'.2) z.2
      · rw [hzz]; exact (invSub Q j hQab).mul_mem v'.2 ((invSub Q j hQab).inv_mem v.2)
    have hz : (z : G) = z' := by
      calc (z : G) = z' * ((z' : G)⁻¹ * z) := by group
        _ = z' := by rw [h1, mul_one]
    have hv : (v : G) = v' := by
      rw [hz] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext hz) (Subtype.ext hv)
  · rintro ⟨u, hu⟩
    obtain ⟨z, hz, v, hv, rfl⟩ := exists_centQ_mul_invSub (hQab := hQab) hodd hjQ hj2 hu
    exact ⟨(⟨z, hz⟩, ⟨v, hv⟩), rfl⟩

section Root

variable {a b : Ω}

theorem conj_mem_invSub (hQ : IsRootSubgroup Q a) (hb : b ≠ a)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    (hj : j ∈ pairStab G a b) {g : G} (hg : g • a = a) {v : G} (hv : v ∈ invSub Q j hQab) :
    g * v * g⁻¹ ∈ invSub Q j hQab := by
  obtain ⟨x, hx, t, ht, rfl⟩ := hQ.exists_mul_pairStab hb hg
  have htv : t * v * t⁻¹ ∈ Q := hQ.normal t ht.1 v hv.1
  have hxc : x * (t * v * t⁻¹) = (t * v * t⁻¹) * x := hQab _ hx _ htv
  have heq : x * t * v * (x * t)⁻¹ = t * v * t⁻¹ := by
    calc x * t * v * (x * t)⁻¹ = x * (t * v * t⁻¹) * x⁻¹ := by group
      _ = (t * v * t⁻¹) * x * x⁻¹ := by rw [hxc]
      _ = t * v * t⁻¹ := by group
  rw [heq]
  refine ⟨htv, ?_⟩
  have hjt : j * t = t * j := hcomm j hj t ht
  calc j * (t * v * t⁻¹) * j⁻¹ = (j * t) * v * (j * t)⁻¹ := by group
    _ = (t * j) * v * (t * j)⁻¹ := by rw [hjt]
    _ = t * (j * v * j⁻¹) * t⁻¹ := by group
    _ = t * v⁻¹ * t⁻¹ := by rw [hv.2]
    _ = (t * v * t⁻¹)⁻¹ := by group

end Root

@[expose] def SameLevel (Q : Subgroup G) (j : G) (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (a c x y : Ω) : Prop :=
  ∃ g : G, g • a = c ∧ ∃ v ∈ invSub Q j hQab, (g * v * g⁻¹) • x = y

theorem sameLevel_smul_iff {a : Ω} (k : G) {c x y : Ω} :
    SameLevel Q j hQab a (k • c) (k • x) (k • y) ↔ SameLevel Q j hQab a c x y := by
  constructor
  · rintro ⟨g, hg, v, hv, hvx⟩
    refine ⟨k⁻¹ * g, by rw [mul_smul, hg, inv_smul_smul], v, hv, ?_⟩
    rw [show k⁻¹ * g * v * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * v * g⁻¹) * k by group, mul_smul, mul_smul,
      hvx, inv_smul_smul]
  · rintro ⟨g, hg, v, hv, hvx⟩
    refine ⟨k * g, by rw [mul_smul, hg], v, hv, ?_⟩
    rw [show k * g * v * (k * g)⁻¹ = k * (g * v * g⁻¹) * k⁻¹ by group, mul_smul, mul_smul,
      inv_smul_smul, hvx]

theorem sameLevel_base_iff {a b : Ω} (hQ : IsRootSubgroup Q a) (hb : b ≠ a)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    (hj : j ∈ pairStab G a b) {x y : Ω} :
    SameLevel Q j hQab a a x y ↔ ∃ v ∈ invSub Q j hQab, v • x = y := by
  constructor
  · rintro ⟨g, hg, v, hv, hvx⟩
    exact ⟨g * v * g⁻¹, conj_mem_invSub hQ hb hcomm hj hg hv, hvx⟩
  · rintro ⟨v, hv, hvx⟩
    exact ⟨1, one_smul _ _, v, hv, by simpa using hvx⟩

end AbelianQ

end CFSG.UnitaryThreeRecognition
