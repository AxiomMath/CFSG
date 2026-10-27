module

public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9Model

public section

namespace CFSG.Quasithin.H13.Q8SqE9

open QuaternionGroup Subgroup

variable {G : Type*} [Group G] {A B : Subgroup G}

namespace Cfg

theorem phiB_a2 (h : Cfg A B) : h.phiB (a 2) = h.z := by
  have h1 : h.phiA (a 2) * h.phiB (a 2) = 1 := h.pi_kappa
  have h2 : h.phiB (a 2) = (h.phiA (a 2))⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [h2]
  exact inv_eq_of_mul_eq_one_right h.z_mul_self

theorem z_mem_B (h : Cfg A B) : h.z ∈ B := h.phiB_a2 ▸ h.phiB_mem _

theorem z_comm_sup (h : Cfg A B) {x : G} (hx : x ∈ A ⊔ B) : x * h.z = h.z * x := by
  obtain ⟨⟨u, v⟩, rfl⟩ := (h.mem_sup_iff x).mp hx
  rw [pi_apply]
  simp only
  have h1 : h.phiA u * h.z = h.z * h.phiA u := by
    rw [z, ← map_mul, ← map_mul, q8_a2_central]
  have h2 : h.phiB v * h.z = h.z * h.phiB v := (h.commute_phi (a 2) v).eq.symm
  rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

theorem mem_inf_iff (h : Cfg A B) (x : G) : x ∈ A ⊓ B ↔ x = 1 ∨ x = h.z := by
  constructor
  · rintro ⟨hxA, hxB⟩
    obtain ⟨u, rfl⟩ := h.exists_phiA hxA
    obtain ⟨v, hv⟩ := h.exists_phiB hxB
    have h1 : h.pi (u, v⁻¹) = 1 := by
      rw [pi_apply]
      simp only [map_inv]
      rw [← hv, mul_inv_cancel]
    rcases (h.pi_eq_one_iff _).mp h1 with h2 | h2
    · left
      have : u = 1 := congrArg Prod.fst h2
      rw [this, map_one]
    · right
      have : u = a 2 := congrArg Prod.fst h2
      rw [this, z]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact ⟨h.z_mem_A, h.z_mem_B⟩

theorem center_iff (h : Cfg A B) {x : G} (hx : x ∈ A ⊔ B) :
    (∀ q ∈ A ⊔ B, x * q = q * x) ↔ x = 1 ∨ x = h.z := by
  constructor
  · intro hc
    obtain ⟨⟨u, v⟩, rfl⟩ := (h.mem_sup_iff x).mp hx
    have hq : ∀ q ∈ A ⊔ B, h.phiA u * h.phiB v * q = q * (h.phiA u * h.phiB v) := hc
    have hu : ∀ w : Q8, u * w = w * u := by
      intro w
      apply h.phiA_inj
      rw [map_mul, map_mul]
      have h1 := hq (h.phiA w) (Subgroup.mem_sup_left (h.phiA_mem w))
      have h2 : h.phiA u * h.phiB v * h.phiA w = h.phiA u * h.phiA w * h.phiB v := by
        rw [mul_assoc, ← (h.commute_phi w v).eq, ← mul_assoc]
      have h3 : h.phiA w * (h.phiA u * h.phiB v) = h.phiA w * h.phiA u * h.phiB v :=
        (mul_assoc _ _ _).symm
      rw [h2, h3] at h1
      exact mul_right_cancel h1
    have hv : ∀ w : Q8, v * w = w * v := by
      intro w
      apply h.phiB_inj
      rw [map_mul, map_mul]
      have h1 := hq (h.phiB w) (Subgroup.mem_sup_right (h.phiB_mem w))
      have h2 : h.phiB w * (h.phiA u * h.phiB v) = h.phiA u * (h.phiB w * h.phiB v) := by
        rw [← mul_assoc, ← (h.commute_phi u w).eq, mul_assoc]
      rw [mul_assoc, h2] at h1
      exact mul_left_cancel h1
    rcases q8_central u hu with rfl | rfl <;> rcases q8_central v hv with rfl | rfl
    · left; simp [pi_apply]
    · right; simp [pi_apply, phiB_a2]
    · right; simp [pi_apply, z]
    · left; rw [pi_apply]; simp only [phiB_a2]; exact h.z_mul_self
  · rintro (rfl | rfl) q hq
    · rw [one_mul, mul_one]
    · exact (h.z_comm_sup hq).symm

theorem mem_of_comm (h : Cfg A B) {x : G} (hx : x ∈ A ⊔ B) (hc : ∀ b ∈ B, x * b = b * x) :
    x ∈ A := by
  obtain ⟨⟨u, v⟩, rfl⟩ := (h.mem_sup_iff x).mp hx
  have hv : ∀ w : Q8, v * w = w * v := by
    intro w
    apply h.phiB_inj
    rw [map_mul, map_mul]
    have h1 := hc (h.phiB w) (h.phiB_mem w)
    rw [pi_apply] at h1
    simp only at h1
    have h2 : h.phiB w * (h.phiA u * h.phiB v) = h.phiA u * (h.phiB w * h.phiB v) := by
      rw [← mul_assoc, ← (h.commute_phi u w).eq, mul_assoc]
    rw [mul_assoc, h2] at h1
    exact mul_left_cancel h1
  rcases q8_central v hv with rfl | rfl
  · simpa [pi_apply] using h.phiA_mem u
  · rw [pi_apply]
    simp only [phiB_a2]
    exact A.mul_mem (h.phiA_mem u) h.z_mem_A

theorem q8_mem_of_gen {X : Subgroup G} (ι : Q8 →* G) (h1 : ι (a 1) ∈ X) (h2 : ι (xa 0) ∈ X)
    (q : Q8) : ι q ∈ X := by
  cases q with
  | a k =>
    have : (a k : Q8) = a 1 ^ k.val := by rw [a_one_pow, ZMod.natCast_zmod_val]
    rw [this, map_pow]
    exact X.pow_mem h1 _
  | xa k =>
    have : (xa k : Q8) = xa 0 * a 1 ^ k.val := by
      rw [a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add]
    rw [this, map_mul, map_pow]
    exact X.mul_mem h2 (X.pow_mem h1 _)

theorem phiB_mem_A (h : Cfg A B) {v : Q8} (hv : v = 1 ∨ v = a 2) : h.phiB v ∈ A := by
  rcases hv with rfl | rfl
  · rw [map_one]; exact one_mem _
  · rw [phiB_a2]; exact h.z_mem_A

theorem phiA_mem_B (h : Cfg A B) {u : Q8} (hu : u = 1 ∨ u = a 2) : h.phiA u ∈ B := by
  rcases hu with rfl | rfl
  · rw [map_one]; exact one_mem _
  · exact h.z_mem_B

theorem finite_A (h : Cfg A B) : Finite A := Finite.of_equiv _ h.eA.some.symm.toEquiv

theorem finite_B (h : Cfg A B) : Finite B := h.symm.finite_A

theorem eq_or_eq (h : Cfg A B) {S : Subgroup G} (hS : S ≤ A ⊔ B) (e : S ≃* Q8) :
    S = A ∨ S = B := by
  let ι : Q8 →* G := S.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.symm.injective
  have hιS : ∀ q, ι q ∈ S := fun q => (e.symm q).2
  have hι' : ∀ s ∈ S, ∃ q, ι q = s := fun s hs => ⟨e ⟨s, hs⟩, by simp [ι]⟩
  obtain ⟨m₁, hm₁⟩ := (h.mem_sup_iff (ι (a 1))).mp (hS (hιS _))
  obtain ⟨m₂, hm₂⟩ := (h.mem_sup_iff (ι (xa 0))).mp (hS (hιS _))
  have e1 : (a 1 : Q8) ^ 2 ≠ 1 := by decide +kernel
  have e2 : (xa 0 : Q8) ^ 2 = a 1 ^ 2 := by decide +kernel
  have e3 : (xa 0 : Q8) * a 1 * (xa 0)⁻¹ = (a 1)⁻¹ := by decide +kernel
  have c1 : m₁ ^ 2 ≠ 1 ∧ m₁ ^ 2 ≠ kappa := by
    constructor
    · intro h1
      apply e1
      apply hι
      rw [map_pow, ← hm₁, ← map_pow, h1, map_one, map_one]
    · intro h1
      apply e1
      apply hι
      rw [map_pow, ← hm₁, ← map_pow, h1, pi_kappa, map_one]
  have c2 : m₂ ^ 2 = m₁ ^ 2 ∨ m₂ ^ 2 = m₁ ^ 2 * kappa := by
    refine (h.pi_eq_iff (m₁ ^ 2) (m₂ ^ 2)).mp ?_
    rw [map_pow, map_pow, hm₁, hm₂, ← map_pow, ← map_pow, e2]
  have c3 : m₂ * m₁ * m₂⁻¹ = m₁⁻¹ ∨ m₂ * m₁ * m₂⁻¹ = m₁⁻¹ * kappa := by
    refine (h.pi_eq_iff m₁⁻¹ (m₂ * m₁ * m₂⁻¹)).mp ?_
    rw [map_inv, map_mul, map_mul, map_inv, hm₁, hm₂, ← map_inv, ← map_mul, ← map_inv,
      ← map_mul, e3]
  have hcard : Nat.card S = 8 := by rw [Nat.card_congr e.toEquiv, card_q8]
  rcases q8sq_pair m₁ m₂ c1 c2 c3 with ⟨hA1, hA2⟩ | ⟨hB1, hB2⟩
  · left
    have hi : ι (a 1) ∈ A := by
      rw [← hm₁, pi_apply]; exact A.mul_mem (h.phiA_mem _) (h.phiB_mem_A hA1)
    have hj : ι (xa 0) ∈ A := by
      rw [← hm₂, pi_apply]; exact A.mul_mem (h.phiA_mem _) (h.phiB_mem_A hA2)
    have hSA : S ≤ A := fun s hs => by
      obtain ⟨q, rfl⟩ := hι' s hs
      exact q8_mem_of_gen ι hi hj q
    have := h.finite_A
    exact Subgroup.eq_of_le_of_card_ge hSA (by rw [h.card_A, hcard])
  · right
    have hi : ι (a 1) ∈ B := by
      rw [← hm₁, pi_apply]; exact B.mul_mem (h.phiA_mem_B hB1) (h.phiB_mem _)
    have hj : ι (xa 0) ∈ B := by
      rw [← hm₂, pi_apply]; exact B.mul_mem (h.phiA_mem_B hB2) (h.phiB_mem _)
    have hSB : S ≤ B := fun s hs => by
      obtain ⟨q, rfl⟩ := hι' s hs
      exact q8_mem_of_gen ι hi hj q
    have := h.finite_B
    exact Subgroup.eq_of_le_of_card_ge hSB (by rw [h.card_B, hcard])

end Cfg

end CFSG.Quasithin.H13.Q8SqE9
