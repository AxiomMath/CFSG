module

public import CFSG.Sporadic.Schreier.MathieuSylowAutMain

public section

namespace CFSG.Quasithin.ModH.SylowCore

open CFSG.Certificates CFSG.Monster.B.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier

variable {n : ℕ}

@[expose] def StrongSylow (X : Type) [Group X] : Prop :=
  ∃ (P : Sylow 2 X) (z : X), z ∈ (P : Subgroup X) ∧ (∀ t ∈ (P : Subgroup X), z * t = t * z) ∧
    ∀ α : MulAut X, (∀ t ∈ (P : Subgroup X), α t = t) → α = 1 ∨ α = MulAut.conj z

theorem StrongSylow.of_equiv {X Y : Type} [Group X] [Group Y] [Finite Y] (e : X ≃* Y)
    (h : StrongSylow Y) : StrongSylow X := by
  obtain ⟨P, z, hz, hzc, hα⟩ := h
  let P' : Sylow 2 X := Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective P
  have hmem : ∀ x : X, x ∈ (P' : Subgroup X) ↔ e x ∈ (P : Subgroup Y) := fun x => by
    show x ∈ Subgroup.map e.symm.toMonoidHom (P : Subgroup Y) ↔ _
    rw [Subgroup.mem_map_equiv]
    simp
  refine ⟨P', e.symm z, (hmem _).2 (by simpa using hz), fun t ht => ?_, fun α hfix => ?_⟩
  · have ht' := hzc (e t) ((hmem t).1 ht)
    apply e.injective
    simpa using ht'
  · set β : MulAut Y := (e.symm.trans α).trans e with hβ
    have hβapp : ∀ y, β y = e (α (e.symm y)) := fun y => rfl
    have hβfix : ∀ t ∈ (P : Subgroup Y), β t = t := by
      intro t ht
      have h1 : e.symm t ∈ (P' : Subgroup X) := (hmem _).2 (by simpa using ht)
      rw [hβapp, hfix _ h1]
      simp
    rcases hα β hβfix with h1 | h1
    · left
      refine MulEquiv.ext fun x => ?_
      have := congrArg (fun f : MulAut Y => f (e x)) h1
      simp only [hβapp, MulEquiv.symm_apply_apply, MulAut.one_apply] at this
      exact e.injective this
    · right
      refine MulEquiv.ext fun x => ?_
      have := congrArg (fun f : MulAut Y => f (e x)) h1
      simp only [hβapp, MulEquiv.symm_apply_apply, MulAut.conj_apply] at this
      apply e.injective
      rw [this]
      simp [MulAut.conj_apply]

theorem StrongSylow.pointwise {X : Type} [Group X] [Finite X] (h : StrongSylow X) :
    ∀ (T : Sylow 2 X) (α : MulAut X), (∀ t ∈ (T : Subgroup X), α t = t) →
      ∃ z : (T : Subgroup X), z ∈ Subgroup.center (T : Subgroup X) ∧
        ∀ g : X, α g = (z : X) * g * (z : X)⁻¹ := by
  obtain ⟨P, z, hz, hzc, hα⟩ := h
  refine sylow_pointwise_inner_of_one P ?_
  intro α hfix
  rcases hα α hfix with rfl | rfl
  · exact ⟨1, (P : Subgroup X).one_mem, fun t _ => by simp, fun g => by simp⟩
  · exact ⟨z, hz, hzc, fun g => by simp [MulAut.conj_apply]⟩

theorem StrongSylow.exists_center_small {X : Type} [Group X] (h : StrongSylow X)
    (hZ : Subgroup.center X = ⊥) :
    ∃ P : Sylow 2 X, ∀ x y : X, x ∈ (P : Subgroup X) → y ∈ (P : Subgroup X) →
      (∀ t ∈ (P : Subgroup X), x * t = t * x) → (∀ t ∈ (P : Subgroup X), y * t = t * y) →
        x = 1 ∨ y = 1 ∨ x = y := by
  obtain ⟨P, z, hz, hzc, hα⟩ := h
  have key : ∀ x : X, (∀ t ∈ (P : Subgroup X), x * t = t * x) → x = 1 ∨ x = z := by
    intro x hxc
    have hfix : ∀ t ∈ (P : Subgroup X), (MulAut.conj x) t = t := by
      intro t ht
      rw [MulAut.conj_apply, hxc t ht, mul_inv_cancel_right]
    have hmem : ∀ w : X, (∀ g : X, w * g * w⁻¹ = g) → w = 1 := by
      intro w hw
      have : w ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := hw g
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      rw [hZ] at this
      exact (Subgroup.mem_bot).1 this
    rcases hα _ hfix with h1 | h1
    · left
      refine hmem x fun g => ?_
      have := congrArg (fun f : MulAut X => f g) h1
      simpa [MulAut.conj_apply] using this
    · right
      have h2 : z⁻¹ * x = 1 := by
        refine hmem _ fun g => ?_
        have := congrArg (fun f : MulAut X => f g) h1
        simp only [MulAut.conj_apply] at this
        calc z⁻¹ * x * g * (z⁻¹ * x)⁻¹ = z⁻¹ * (x * g * x⁻¹) * z := by group
          _ = z⁻¹ * (z * g * z⁻¹) * z := by rw [this]
          _ = g := by group
      exact (inv_mul_eq_one.1 h2).symm
  refine ⟨P, fun x y _ _ hxc hyc => ?_⟩
  rcases key x hxc with rfl | rfl
  · exact Or.inl rfl
  · rcases key y hyc with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

end CFSG.Quasithin.ModH.SylowCore
