module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoExcDefs
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.RootSystem

theorem levTwoS3a_data_congr {ι : Type} [Fintype ι] [DecidableEq ι] {R R' : Matrix ι ι ℤ}
    (h : R = R') (hR : TauCeti.IsFiniteType R) (hR' : TauCeti.IsFiniteType R')
    (p : ℕ) (c : ι → ZMod p) (Φ : Set (ι → ℤ)) :
    LevTwoData hR p c Φ ↔ LevTwoData hR' p c Φ := by
  subst h
  rw [Subsingleton.elim hR hR']

theorem levTwoS3a_isRt_iff {τ : Tag} {β : Fin τ.rank → ℤ} :
    IsRt (isFiniteType_cartan τ) β ↔ IsRoot τ β := by
  rw [isRoot_iff_exists_smul_single]
  simp only [IsRt, smul_def]

theorem levTwoS3a_rRefl_eq
    {τ : Tag} (β : Fin τ.rank → ℤ) :
    rRefl (isFiniteType_cartan τ) β = rootReflection β := by
  by_cases hβ : IsRoot τ β
  · obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 hβ
    rw [rRefl_eq_conj (isFiniteType_cartan τ) hw, rootReflection_eq_conj hw]
  · have hβ' : ¬ IsRt (isFiniteType_cartan τ) β := fun hr => hβ (levTwoS3a_isRt_iff.1 hr)
    simp [rRefl, rootReflection, hβ, hβ']

theorem levTwoS3a_weylAction_eq {τ : Tag} (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    weylAction (isFiniteType_cartan τ) w v = w • v := smul_def w v

theorem levTwoS3a_form_eq (τ : Tag) :
    ∃ κ : ℚ, 0 < κ ∧ ∀ u v : Fin τ.rank → ℤ,
      form (isFiniteType_cartan τ) (toRat u) (toRat v) = κ * (iform u v : ℚ) := by
  obtain ⟨κ, hκ, hd⟩ := exists_symmetrizer_eq τ
  refine ⟨κ, hκ, ?_⟩
  have hmat : symmetrized (isFiniteType_cartan τ) =
      κ • (τ.symmetrizedCartan.map (Int.cast : ℤ → ℚ)) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, symmetrized_cartan_apply,
      symmetrizedCartan_apply]
    push_cast
    rw [hd i]
    ring
  intro u v
  rw [form_apply, hmat, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  rw [iform]
  push_cast
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, toRat_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem levTwoS3a_form_ne_zero_iff {τ : Tag} {κ : ℚ} (hκ : κ ≠ 0)
    (hform : ∀ u v : Fin τ.rank → ℤ,
      form (isFiniteType_cartan τ) (toRat u) (toRat v) = κ * (iform u v : ℚ))
    {u v : Fin τ.rank → ℤ} :
    form (isFiniteType_cartan τ) (toRat u) (toRat v) ≠ 0 ↔ iform u v ≠ 0 := by
  rw [hform u v]
  constructor
  · intro h h0
    exact h (by simp [h0])
  · intro h h0
    exact h (by
      have := (mul_eq_zero.mp h0).resolve_left hκ
      exact_mod_cast this)

theorem levTwoS3a_form_norm_eq_iff {τ : Tag} {κ : ℚ} (hκ : κ ≠ 0)
    (hform : ∀ u v : Fin τ.rank → ℤ,
      form (isFiniteType_cartan τ) (toRat u) (toRat v) = κ * (iform u v : ℚ))
    {u v : Fin τ.rank → ℤ} :
    form (isFiniteType_cartan τ) (toRat u) (toRat u) =
      form (isFiniteType_cartan τ) (toRat v) (toRat v) ↔ iform u u = iform v v := by
  rw [hform u u, hform v v]
  constructor
  · intro h
    exact_mod_cast mul_left_cancel₀ hκ h
  · intro h
    rw [h]

theorem levTwoS3a_tcRoot_congr {ι : Type} [Fintype ι] [DecidableEq ι] {R R' : Matrix ι ι ℤ}
    (h : R = R') (hR : TauCeti.IsFiniteType R) (hR' : TauCeti.IsFiniteType R')
    (Φ : Set (ι → ℤ)) : TCRoot hR Φ ↔ TCRoot hR' Φ := by
  subst h
  rw [Subsingleton.elim hR hR']

end CFSG.StandardType.LevTwo
