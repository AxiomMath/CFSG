module

public import CFSG.RankThree.S4Free.StellmacherW

public section

namespace CFSG.RankThree.S4Free.Stell33

open Subgroup

universe u

inductive IsF1Fusion (𝒦 : HostClass) {S : Type u} [Group S] (P : Subgroup S) :
    (P →* S) → Prop
  | refl : IsF1Fusion 𝒦 P P.subtype
  | step {φ ψ : P →* S} (hφ : IsF1Fusion 𝒦 P φ) {X : Type u} [Group X] (ι : S →* X)
      (hι : F1Host 𝒦 ι) (k : X) (hψ : ∀ p, ι (ψ p) = k * ι (φ p) * k⁻¹) : IsF1Fusion 𝒦 P ψ

variable {𝒦 : HostClass} {S : Type u} [Group S] {P : Subgroup S}

theorem IsF1Fusion.injective {φ : P →* S} (h : IsF1Fusion 𝒦 P φ) : Function.Injective φ := by
  induction h with
  | refl => exact P.subtype_injective
  | step _ ι hι k hψ ih =>
    intro p q hpq
    apply ih
    apply hι.admissible.injective
    have h1 := congrArg ι hpq
    rw [hψ, hψ] at h1
    exact mul_left_cancel (mul_right_cancel h1)

theorem IsF1Fusion.mem_stellW_iff [Finite S] {φ : P →* S} (h : IsF1Fusion 𝒦 P φ) (p : P) :
    φ p ∈ stellW 𝒦 S ↔ (p : S) ∈ stellW 𝒦 S := by
  induction h with
  | refl => rfl
  | @step φ ψ _ X _ ι hι k hψ ih =>
    have hinj := hι.admissible.injective
    have hn := stellW_normal hι
    have e1 : ψ p ∈ stellW 𝒦 S ↔ ι (ψ p) ∈ (stellW 𝒦 S).map ι := (mem_map_iff_mem hinj).symm
    have e2 : φ p ∈ stellW 𝒦 S ↔ ι (φ p) ∈ (stellW 𝒦 S).map ι := (mem_map_iff_mem hinj).symm
    rw [e1, hψ, ← ih, e2]
    refine ⟨fun hx => ?_, fun hx => hn.conj_mem _ hx k⟩
    have h1 := hn.conj_mem _ hx k⁻¹
    rwa [show k⁻¹ * (k * ι (φ p) * k⁻¹) * k⁻¹⁻¹ = ι (φ p) by group] at h1

theorem IsF1Fusion.exists_eq_of_mem_stellW [Finite S] {φ : P →* S} (h : IsF1Fusion 𝒦 P φ)
    (hWP : stellW 𝒦 S ≤ P) {w : S} (hw : w ∈ stellW 𝒦 S) : ∃ p : P, φ p = w := by
  induction h generalizing w with
  | refl => exact ⟨⟨w, hWP hw⟩, rfl⟩
  | @step φ ψ _ X _ ι hι k hψ ih =>
    have hn := stellW_normal hι
    have h1 : k⁻¹ * ι w * k ∈ (stellW 𝒦 S).map ι := by
      have := hn.conj_mem _ ⟨w, hw, rfl⟩ k⁻¹
      rwa [inv_inv] at this
    obtain ⟨w', hw', hw'e⟩ := h1
    obtain ⟨p, hp⟩ := ih hw'
    refine ⟨p, hι.admissible.injective ?_⟩
    rw [hψ, hp, hw'e]
    group

theorem IsF1Fusion.exists_step {φ : P →* S} (h : IsF1Fusion 𝒦 P φ) {X : Type u} [Group X]
    {ι : S →* X} (hι : F1Host 𝒦 ι) (k : X) (hk : ∀ p, k * ι (φ p) * k⁻¹ ∈ ι.range) :
    ∃ ψ : P →* S, IsF1Fusion 𝒦 P ψ ∧ ∀ p, ι (ψ p) = k * ι (φ p) * k⁻¹ := by
  let f : P →* X := (MulAut.conj k).toMonoidHom.comp (ι.comp φ)
  have hf : ∀ p, f p ∈ ι.range := hk
  let ψ : P →* S := (MonoidHom.ofInjective hι.admissible.injective).symm.toMonoidHom.comp
    (f.codRestrict ι.range hf)
  have hψ : ∀ p, ι (ψ p) = k * ι (φ p) * k⁻¹ := fun p => by
    simp [ψ, f]
  exact ⟨ψ, h.step ι hι k hψ, hψ⟩

end CFSG.RankThree.S4Free.Stell33
