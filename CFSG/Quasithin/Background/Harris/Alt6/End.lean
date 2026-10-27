module

public import CFSG.Quasithin.Background.Harris.Alt6.Heart
public import CFSG.Quasithin.Background.Harris.L2.Natural

public section

namespace CFSG.Quasithin.G11.Harris.Alt6

open CFSG.Quasithin.G11 CFSG.CharacterTheory.SteinbergBY AlternatingSix Equiv Matrix
  CFSG.Quasithin.Background.Harris.OrdinaryProofs

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def coordMatrix (T : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2))
    (f : Module.End (ZMod 2) V) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  LinearMap.toMatrix' (T.toLinearMap ∘ₗ f ∘ₗ T.symm.toLinearMap)

theorem coordMatrix_mulVec (T : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) (f : Module.End (ZMod 2) V)
    (v : V) : coordMatrix T f *ᵥ T v = T (f v) := by
  have := Matrix.toLin'_apply (coordMatrix T f) (T v)
  rw [coordMatrix, Matrix.toLin'_toMatrix'] at this
  show LinearMap.toMatrix' _ *ᵥ T v = _
  rw [← this]
  simp

theorem toMatrix_commute {L : Subgroup (GLV V)} {f : Module.End (ZMod 2) V}
    (hf : f ∈ endCommutant L) (T : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) {l : ↥L}
    {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hM : ∀ v, T ((l : GLV V) v) = M *ᵥ T v) :
    coordMatrix T f * M = M * coordMatrix T f := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun w => ?_
  obtain ⟨v, rfl⟩ := T.surjective w
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_apply, LinearMap.comp_apply,
    Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, ← hM v,
    coordMatrix_mulVec, coordMatrix_mulVec, endCommutant_apply_comm hf l.2 v, hM (f v)]

theorem natCard_endCommutant_two [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤)
    (T : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) {l₁ l₂ : ↥L} {M₁ M₂ : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h₁ : ∀ v, T ((l₁ : GLV V) v) = M₁ *ᵥ T v) (h₂ : ∀ v, T ((l₂ : GLV V) v) = M₂ *ᵥ T v)
    (hc : ∀ X : Matrix (Fin 4) (Fin 4) (ZMod 2), X * M₁ = M₁ * X → X * M₂ = M₂ * X →
      X = 0 ∨ X = 1) : Nat.card (endCommutant L) = 2 ^ 1 := by
  have : Nontrivial (endCommutant L) := endCommutant_nontrivial hL
  rw [pow_one, Nat.card_eq_two_iff]
  refine ⟨0, 1, zero_ne_one, ?_⟩
  ext ⟨f, hf⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases hc _ (toMatrix_commute hf T h₁) (toMatrix_commute hf T h₂) with h | h
  · left
    apply Subtype.ext
    refine LinearMap.ext fun v => ?_
    apply T.injective
    rw [← coordMatrix_mulVec, h]
    simp
  · right
    apply Subtype.ext
    refine LinearMap.ext fun v => ?_
    apply T.injective
    rw [← coordMatrix_mulVec, h]
    simp

theorem endIsField_one [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤)
    (e : ↥L ≃* alternatingGroup (Fin 6)) (T : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2))
    (hT : (∀ (l : ↥L) (v : V), T ((l : GLV V) v) = heartHom (e l : Perm (Fin 6)) *ᵥ T v) ∨
      (∀ (l : ↥L) (v : V),
        T ((l : GLV V) v) = heartHom (totalPermHom (e l : Perm (Fin 6))) *ᵥ T v)) :
    EndIsField L 1 := by
  refine CFSG.Quasithin.G11.Harris.L2.endIsField_of_natCard hL ?_
  rcases hT with hT | hT
  · refine natCard_endCommutant_two hL T (l₁ := e.symm ⟨cyc5, cyc5_mem⟩)
      (l₂ := e.symm ⟨cyc3, cyc3_mem⟩) (M₁ := heartHom cyc5) (M₂ := heartHom cyc3)
      (fun v => ?_) (fun v => ?_) fun X h5 h3 => commutant_heart_a X h5 h3
    · rw [hT]; simp
    · rw [hT]; simp
  · refine natCard_endCommutant_two hL T (l₁ := e.symm ⟨cyc5, cyc5_mem⟩)
      (l₂ := e.symm ⟨cyc3, cyc3_mem⟩) (M₁ := heartHom (totalPermHom cyc5))
      (M₂ := heartHom (totalPermHom cyc3)) (fun v => ?_) (fun v => ?_)
      fun X h5 h3 => commutant_heart_b X h5 h3
    · rw [hT]; simp
    · rw [hT]; simp

end CFSG.Quasithin.G11.Harris.Alt6
