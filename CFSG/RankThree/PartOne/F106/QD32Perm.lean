module

public import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial
public import CFSG.RankThree.PartOne.N143X.Weights

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement

attribute [local instance] qdFintypeD

theorem qd32_mul_mul_inv_mem_zpowers (a b : QD32) : a * b * (b * a)⁻¹ ∈ zpowers qd32Z := by
  rw [← quaternion_dihedral_extraspecial_involution_generation.2.2.2.2.2.2.2.2.1]
  have e : a * b * (b * a)⁻¹ = ⁅a, b⁆ := by
    rw [commutatorElement_def]
    group
  rw [e, commutator_eq_closure]
  exact subset_closure (commutator_mem_commutatorSet a b)

theorem qd32_mul_self_mem_zpowers (a : QD32) : a * a ∈ zpowers qd32Z := by
  have hel := quaternion_dihedral_extraspecial_involution_generation.2.2.2.2.2.2.2.2.2.2.1
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hel.exponent_dvd_p
    (a : QD32 ⧸ zpowers qd32Z)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, sq] at h
  exact h

theorem qd32_comm_involutions_key : ∀ g h : QuaternionGroup 2 × QuaternionDihedralD,
    qdSameImage (g * g) 1 → qdSameImage (h * h) 1 → qdSameImage (g * h) (h * g) →
    ¬ qdSameImage g 1 → ¬ qdSameImage h 1 → ¬ qdSameImage g h →
    qdSameImage g (QuaternionGroup.a 2, 1) ∨ qdSameImage h (QuaternionGroup.a 2, 1) ∨
      qdSameImage (g * h) (QuaternionGroup.a 2, 1) := by
  decide +kernel

theorem qd32_comm_involutions (x y : QD32) (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    x = qd32Z ∨ y = qd32Z ∨ x * y = qd32Z := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_one, qd32_mk_eq_mk_iff] at hx hy
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, qd32_mk_eq_mk_iff] at hxy
  rw [← QuotientGroup.mk_one, Ne, qd32_mk_eq_mk_iff] at hx1 hy1
  rw [Ne, qd32_mk_eq_mk_iff] at hne
  rw [qd32Z_eq, ← QuotientGroup.mk_mul, qd32_mk_eq_mk_iff, qd32_mk_eq_mk_iff,
    qd32_mk_eq_mk_iff]
  exact qd32_comm_involutions_key g h hx hy hxy hx1 hy1 hne

instance instFiniteQD32 : Finite QD32 :=
  Nat.finite_of_card_ne_zero (by rw [card_QD32]; norm_num)

theorem qd32_card_le_two_of_not_mem {H : Subgroup QD32} (hz : qd32Z ∉ H) : Nat.card H ≤ 2 := by
  classical
  have hsq : ∀ h ∈ H, h * h = 1 := by
    intro h hh
    rcases (mem_zpowers_qd32Z _).1 (qd32_mul_self_mem_zpowers h) with h2 | h2
    · exact h2
    · exact absurd (h2 ▸ H.mul_mem hh hh) hz
  have hcomm : ∀ h ∈ H, ∀ k ∈ H, h * k = k * h := by
    intro h hh k hk
    rcases (mem_zpowers_qd32Z _).1 (qd32_mul_mul_inv_mem_zpowers h k) with h2 | h2
    · exact mul_inv_eq_one.mp h2
    · exfalso
      apply hz
      rw [← h2]
      exact H.mul_mem (H.mul_mem hh hk) (H.inv_mem (H.mul_mem hk hh))
  have hone : ∀ a b : H, a ≠ 1 → b ≠ 1 → a = b := by
    intro a b ha hb
    by_contra hne
    rcases qd32_comm_involutions a.1 b.1 (hsq a.1 a.2) (hsq b.1 b.2) (hcomm a.1 a.2 b.1 b.2)
      (fun h => ha (Subtype.ext h)) (fun h => hb (Subtype.ext h))
      (fun h => hne (Subtype.ext h)) with h | h | h
    · exact hz (h ▸ a.2)
    · exact hz (h ▸ b.2)
    · exact hz (h ▸ H.mul_mem a.2 b.2)
  have hinj : Function.Injective (fun a : H => decide (a = 1)) := by
    intro a b hab
    by_cases ha : a = 1
    · by_cases hb : b = 1
      · rw [ha, hb]
      · simp [ha, hb] at hab
    · by_cases hb : b = 1
      · simp [ha, hb] at hab
      · exact hone a b ha hb
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem qd32_faithful_perm_card {S : Type*} [Finite S] (ψ : QD32 →* Equiv.Perm S)
    (hψ : Function.Injective ψ) : 16 ≤ Nat.card S := by
  classical
  have hz1 : ψ qd32Z ≠ 1 := by
    intro h
    have h1 : qd32Z = 1 := hψ (h.trans (map_one ψ).symm)
    have := orderOf_qd32Z
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨x, hx⟩ : ∃ x, ψ qd32Z x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact hz1 (Equiv.ext hcon)
  let _ : MulAction QD32 S := MulAction.compHom S ψ
  have hzH : qd32Z ∉ MulAction.stabilizer QD32 x := fun h => hx h
  have h1 := qd32_card_le_two_of_not_mem hzH
  have h2 : Nat.card (MulAction.orbit QD32 x) * Nat.card (MulAction.stabilizer QD32 x) =
      Nat.card QD32 := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer QD32 x)]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
  have h3 : Nat.card (MulAction.orbit QD32 x) ≤ Nat.card S :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  rw [card_QD32] at h2
  nlinarith

theorem not_exists_qd32_embedding {H : Type} [Group H] {d : ℕ} (hd : d < 16)
    (h : CFSG.RankThree.PartOne.N143X.FaithfulSmall H d) :
    ¬ ∃ f : QD32 →* H, Function.Injective f := by
  obtain ⟨S, hS, φ, hcard, hφ⟩ := h
  rintro ⟨f, hf⟩
  have := qd32_faithful_perm_card (φ.comp f) (hφ.comp hf)
  omega

end CFSG.RankThree.PartOne.F106
