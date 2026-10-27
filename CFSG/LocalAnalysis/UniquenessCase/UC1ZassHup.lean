module

public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassFpf
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

open CFSG.BenderSuzuki.External

section MulAut

variable {A : Type*} [CommSemiring A] {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
  [Module A M]

@[expose] def mulAutOf (ρ : Representation A G M) : G →* MulAut (Multiplicative M) where
  toFun g :=
    { toFun := fun x => Multiplicative.ofAdd (ρ g (Multiplicative.toAdd x))
      invFun := fun x => Multiplicative.ofAdd (ρ g⁻¹ (Multiplicative.toAdd x))
      left_inv := fun x => by simp [← Module.End.mul_apply, ← map_mul]
      right_inv := fun x => by simp [← Module.End.mul_apply, ← map_mul]
      map_mul' := fun x y => by simp }
  map_one' := by
    ext x
    simp
  map_mul' := fun g h => by
    ext x
    simp [Module.End.mul_apply]

theorem mulAutOf_injective {ρ : Representation A G M} (hρ : Function.Injective ρ) :
    Function.Injective (mulAutOf ρ) := by
  intro g h hgh
  refine hρ (LinearMap.ext fun m => ?_)
  have := congrArg
    (fun φ : MulAut (Multiplicative M) => Multiplicative.toAdd (φ (Multiplicative.ofAdd m))) hgh
  simpa [mulAutOf] using this

end MulAut

section Huppert

variable {A : Type*} [CommSemiring A] {G : Type} [Group G] [Finite G] {M : Type}
  [AddCommGroup M] [Module A M] [Finite M] {ρ : Representation A G M}

theorem Fpf.huppert (hf : Fpf ρ) :
    (∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ∀ P : Sylow q (mulAutOf ρ).range, IsCyclic P) ∧
      (∀ P : Sylow 2 (mulAutOf ρ).range,
        IsCyclic P ∨ ∃ k : ℕ, 2 ≤ k ∧ IsPGroup 2 (QuaternionGroup k) ∧
          Nonempty (P ≃* QuaternionGroup k)) ∧
      (∀ p₁ p₂ : ℕ, p₁.Prime → p₂.Prime →
        ∀ H : Subgroup (mulAutOf ρ).range, Nat.card H = p₁ * p₂ → IsCyclic H) := by
  refine huppert_V_8_15_fixedPointFree_automorphism_subgroup_classification
    (G := Multiplicative M) (mulAutOf ρ).range ?_
  rintro ⟨_, h, rfl⟩ hφ x hx
  have hh : h ≠ 1 := by
    rintro rfl
    exact hφ (Subtype.ext (map_one _))
  have hx' : ρ h (Multiplicative.toAdd x) = Multiplicative.toAdd x :=
    congrArg Multiplicative.toAdd hx
  exact toAdd_eq_zero.mp (hf h hh _ hx')

theorem Fpf.isCyclic_of_isPGroup (hρ : Function.Injective ρ) (hf : Fpf ρ) {q : ℕ} [Fact q.Prime]
    (hq : q ≠ 2) {U : Subgroup G} (hU : IsPGroup q U) : IsCyclic U := by
  let e : G ≃* (mulAutOf ρ).range := MonoidHom.ofInjective (mulAutOf_injective hρ)
  obtain ⟨P, hP⟩ := (hU.map e.toMonoidHom).exists_le_sylow
  haveI : IsCyclic P := hf.huppert.1 q hq P
  haveI : IsCyclic (U.map e.toMonoidHom) := Subgroup.isCyclic_of_le hP
  exact (U.equivMapOfInjective e.toMonoidHom e.injective).isCyclic.mpr this

theorem Fpf.isCyclic_sylow (hρ : Function.Injective ρ) (hf : Fpf ρ) {q : ℕ} [Fact q.Prime]
    (hq : q ≠ 2) (P : Sylow q G) : IsCyclic P :=
  hf.isCyclic_of_isPGroup hρ hq P.isPGroup'

theorem Fpf.sylow_two (hρ : Function.Injective ρ) (hf : Fpf ρ) (P : Sylow 2 G) :
    IsCyclic P ∨ ∃ k : ℕ, 2 ≤ k ∧ IsPGroup 2 (QuaternionGroup k) ∧
      Nonempty (P ≃* QuaternionGroup k) := by
  let e : G ≃* (mulAutOf ρ).range := MonoidHom.ofInjective (mulAutOf_injective hρ)
  let Q : Sylow 2 (mulAutOf ρ).range := P.mapSurjective e.surjective
  let eQ : P ≃* Q := (P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
  rcases hf.huppert.2.1 Q with h | ⟨k, hk, hq, ⟨f⟩⟩
  · exact Or.inl (eQ.isCyclic.mpr h)
  · exact Or.inr ⟨k, hk, hq, ⟨eQ.trans f⟩⟩

theorem Fpf.isCyclic_of_card_eq_mul (hρ : Function.Injective ρ) (hf : Fpf ρ) {p₁ p₂ : ℕ}
    (h₁ : p₁.Prime) (h₂ : p₂.Prime) {H : Subgroup G} (hH : Nat.card H = p₁ * p₂) :
    IsCyclic H := by
  let e : G ≃* (mulAutOf ρ).range := MonoidHom.ofInjective (mulAutOf_injective hρ)
  have hcard : Nat.card (H.map e.toMonoidHom) = p₁ * p₂ := by
    rw [← hH]
    exact Subgroup.card_map_of_injective e.injective
  exact (H.equivMapOfInjective e.toMonoidHom e.injective).isCyclic.mpr
    (hf.huppert.2.2 p₁ p₂ h₁ h₂ _ hcard)

end Huppert

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
