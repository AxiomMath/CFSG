module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement

theorem s16c13bc_not_mem_of_perfect {Γ : Type*} [Group Γ] {L Z : Subgroup Γ} {p : ℕ}
    (hp : p.Prime) (hL : _root_.commutator ↥L = ⊤) (hLc : Subgroup.center ↥L = ⊥)
    (hZc : Nat.card Z = p) (hZn : ∀ m ∈ L, ∀ x ∈ Z, m * x * m⁻¹ ∈ Z)
    {ψ : Γ} (hψL : ψ ∈ L) (hψ1 : ψ ≠ 1) : ψ ∉ Z := by
  intro hψZ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZc]; exact hp.ne_zero)
  have hord : orderOf ψ = p := by
    have hd : orderOf ψ ∣ p := by
      have h := orderOf_dvd_natCard (⟨ψ, hψZ⟩ : Z)
      rw [hZc, ← Subgroup.orderOf_coe] at h
      exact h
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hψ1
    · exact h
  have hZgen : Subgroup.zpowers ψ = Z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hψZ) ?_
    rw [Nat.card_zpowers, hord, hZc]
  have hZL : Z ≤ L := hZgen ▸ Subgroup.zpowers_le.2 hψL
  let Y : Subgroup ↥L := Z.subgroupOf L
  haveI hYn : Y.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hZL).2 fun m hm => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hZn m hm x hx, fun hx => ?_⟩
    have h := hZn m⁻¹ (L.inv_mem hm) _ hx
    simpa [mul_assoc] using h
  have hYc : Nat.card Y = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv, hZc]
  haveI : IsCyclic Y := isCyclic_of_prime_card hYc
  have hcommAut : ∀ a b : MulAut ↥Y, a * b = b * a := fun a b =>
    (IsCyclic.mulAutMulEquiv (G := ↥Y)).injective (by rw [map_mul, map_mul, mul_comm])
  let φ : ↥L →* MulAut ↥Y := MulAut.conjNormal
  have hker : (⊤ : Subgroup ↥L) ≤ φ.ker := by
    rw [← hL, _root_.commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcommAut _ _)
  have hψY : (⟨ψ, hψL⟩ : ↥L) ∈ Y := hψZ
  have hψc : (⟨ψ, hψL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : φ g = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top g))
    have h2 := congrArg (fun a : MulAut ↥Y => ((a ⟨⟨ψ, hψL⟩, hψY⟩ : ↥Y) : ↥L)) h1
    simp only [φ, MulAut.conjNormal_apply] at h2
    exact mul_inv_eq_iff_eq_mul.1 h2
  rw [hLc, Subgroup.mem_bot] at hψc
  exact hψ1 (congrArg Subtype.val hψc)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
