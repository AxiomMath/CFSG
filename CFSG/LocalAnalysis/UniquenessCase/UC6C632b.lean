module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup
open scoped commutatorElement

theorem eq_sup_centralizer_of_coprime {G : Type*} [Group G] [Finite G] {K U Y : Subgroup G} {r : ℕ}
    [Fact r.Prime] (hUK : U ≤ K) (hKU : K ≤ normalizer (U : Set G)) (hY : IsPGroup r Y)
    (hYK : Y ≤ normalizer (K : Set G)) (hcomm : ⁅Y, K⁆ ≤ U) (hcop : ¬ r ∣ Nat.card U) :
    K = U ⊔ (K ⊓ centralizer (Y : Set G)) := by
  classical
  refine le_antisymm (fun k hk => ?_) (sup_le hUK inf_le_left)
  let S : Set G := {x | ∃ u ∈ U, x = k * u}
  have hyU : ∀ y ∈ Y, ∀ u ∈ U, y * u * y⁻¹ ∈ U := by
    intro y hy u hu
    have h1 : ⁅y, u⁆ ∈ U := hcomm (Subgroup.commutator_mem_commutator hy (hUK hu))
    have h2 : ⁅y, u⁆ * u ∈ U := U.mul_mem h1 hu
    have h3 : ⁅y, u⁆ * u = y * u * y⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rwa [h3] at h2
  have hyk : ∀ y ∈ Y, y * k * y⁻¹ * k⁻¹ ∈ U := fun y hy =>
    hcomm (Subgroup.commutator_mem_commutator hy hk)
  have hS : ∀ y ∈ Y, ∀ x ∈ S, y * x * y⁻¹ ∈ S := by
    rintro y hy _ ⟨u, hu, rfl⟩
    refine ⟨k⁻¹ * (y * k * y⁻¹) * (y * u * y⁻¹), ?_, ?_⟩
    · have h1 : k⁻¹ * (y * k * y⁻¹) ∈ U := by
        have := (mem_normalizer_iff.1 (hKU (K.inv_mem hk)) (y * k * y⁻¹ * k⁻¹)).1 (hyk y hy)
        simpa [mul_assoc] using this
      exact U.mul_mem h1 (hyU y hy u hu)
    · simp [mul_assoc]
  letI : MulAction Y S :=
    { smul := fun y x => ⟨(y : G) * (x : G) * (y : G)⁻¹, hS y y.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : ↥Y) : G) * (x : G) * ((1 : ↥Y) : G)⁻¹ = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        show ((a * b : ↥Y) : G) * (x : G) * ((a * b : ↥Y) : G)⁻¹ =
          (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card S = Nat.card U := by
    refine Nat.card_congr (Equiv.symm (Equiv.ofBijective (fun u : U => (⟨k * u, u, u.2, rfl⟩ : S)) ⟨?_, ?_⟩))
    · intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simpa using this
    · rintro ⟨x, u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  haveI : Finite S := inferInstance
  obtain ⟨⟨x, hxS⟩, hfix⟩ := hY.nonempty_fixed_point_of_prime_not_dvd_card S (by rw [hcard]; exact hcop)
  obtain ⟨u, hu, rfl⟩ := hxS
  have hfix' : ∀ y ∈ Y, y * (k * u) * y⁻¹ = k * u := by
    intro y hy
    have := MulAction.mem_fixedPoints.1 hfix ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hk1 : k * u ∈ K ⊓ centralizer (Y : Set G) := by
    refine Subgroup.mem_inf.2 ⟨K.mul_mem hk (hUK hu), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := hfix' y hy
    calc y * (k * u) = (y * (k * u) * y⁻¹) * y := by group
      _ = k * u * y := by rw [this]
  have h5 : (k * u) * u⁻¹ ∈ (K ⊓ centralizer (Y : Set G)) ⊔ U :=
    Subgroup.mul_mem_sup hk1 (U.inv_mem hu)
  rw [sup_comm] at h5
  simpa using h5

end CFSG.LocalAnalysis.UniquenessCase.UC6
