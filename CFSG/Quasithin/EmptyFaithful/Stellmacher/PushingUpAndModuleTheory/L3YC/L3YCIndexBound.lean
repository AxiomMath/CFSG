module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCSchurL32

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin

namespace Stellmacher.PU.L3YC

section Abstract

variable {Λ : Type} [Group Λ] [Finite Λ]

theorem card_le_two_mul_of_commutator_le
    [Group.IsPerfect Λ] (N : Subgroup Λ) [N.Normal]
    (Q : Subgroup Λ) [hQn : Q.Normal] (hQ : ⁅N, (⊤ : Subgroup Λ)⁆ ≤ Q) (hQN : Q ≤ N)
    (e : Λ ⧸ N ≃* GL (Fin 3) (ZMod 2)) :
    Nat.card N ≤ 2 * Nat.card Q := by
  classical
  let q0 : Λ →* GL (Fin 3) (ZMod 2) := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hq0s : Function.Surjective q0 := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hq0k : q0.ker = N := by
    ext x
    simp only [MonoidHom.mem_ker, q0, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let q : Λ ⧸ Q →* GL (Fin 3) (ZMod 2) := QuotientGroup.lift Q q0 (by rwa [hq0k])
  have hqmk : ∀ x : Λ, q (QuotientGroup.mk x) = q0 x := fun x => rfl
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := hq0s y
    exact ⟨QuotientGroup.mk x, by rw [hqmk, hx]⟩
  have hqker : q.ker = N.map (QuotientGroup.mk' Q) := by
    ext z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    simp only [MonoidHom.mem_ker, hqmk, Subgroup.mem_map, QuotientGroup.mk'_apply]
    constructor
    · intro h
      exact ⟨x, by rw [← hq0k]; exact h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rw [QuotientGroup.eq] at hyx
      have : x = y * (y⁻¹ * x) := by group
      have hx : x ∈ N := by
        rw [this]; exact N.mul_mem hy (hQN hyx)
      rw [← MonoidHom.mem_ker, hq0k]; exact hx
  have hcentral : q.ker ≤ Subgroup.center (Λ ⧸ Q) := by
    rw [hqker]
    rintro _ ⟨n, hn, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    simp only [QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h : (l * n)⁻¹ * (n * l) = ⁅n⁻¹, l⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [h]
    exact hQ (Subgroup.commutator_mem_commutator (N.inv_mem hn) (Subgroup.mem_top _))
  have hperf : Group.IsPerfect (Λ ⧸ Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
  have hS := card_ker_le_two_of_perfect_central (MulEquiv.refl (GL (Fin 3) (ZMod 2))) q hqs
    hcentral
  rw [hqker] at hS
  let φ : ↥N →* Λ ⧸ Q := (QuotientGroup.mk' Q).comp N.subtype
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hφk : φ.ker = Q.subgroupOf N := by
    ext x
    simp [φ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hφr : φ.range = N.map (QuotientGroup.mk' Q) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hφk, hφr] at h1
  have hcQ : Nat.card ↥(Q.subgroupOf N) = Nat.card ↥Q := by
    rw [← Subgroup.card_map_of_injective N.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hQN]
  rw [hcQ] at h1
  rw [← h1]
  have hpos : 0 < Nat.card ↥Q := Nat.card_pos
  nlinarith

end Abstract

end Stellmacher.PU.L3YC

end CFSG.Quasithin
