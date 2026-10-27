module

public import CFSG.LocalAnalysis.StandardType.StarFour.SemisimpleFrame
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.RingTheory.Norm.Transitivity

public section

namespace CFSG.StandardType.StarFour

variable {F : Type} [Field F] {P : Type} [CommGroup P] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def repCentSL (ρ : P →* (V ≃ₗ[F] V)) : Subgroup (SpecialLinearGroup F V) :=
  (Subgroup.centralizer (Set.range ρ)).comap SpecialLinearGroup.toLinearEquiv

variable {ρ : P →* (V ≃ₗ[F] V)}

@[expose] def SemiFrame.GoodAtBlock (fr : SemiFrame F ρ) (i : Fin fr.r) : Prop :=
  2 ≤ fr.m i ∧ (3 ≤ fr.m i ∨ 4 ≤ Nat.card (fr.E i))

namespace SemiFrame

variable (fr : SemiFrame F ρ)

@[expose] noncomputable def blockUpdate (i : Fin fr.r)
    (B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i)) :
    (∀ j, Fin (fr.m j) → fr.E j) ≃ₗ[F] (∀ j, Fin (fr.m j) → fr.E j) where
  toFun w := Function.update w i (B (w i))
  invFun w := Function.update w i (B⁻¹ (w i))
  map_add' w w' := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [Function.update_self, Pi.add_apply, map_add]
    · simp [Function.update_of_ne hj]
  map_smul' c w := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, Pi.smul_apply, RingHom.id_apply]
      exact LinearMap.map_smul_of_tower
        (B : (Fin (fr.m j) → fr.E j) →ₗ[fr.E j] (Fin (fr.m j) → fr.E j)) c (w j)
    · simp [Function.update_of_ne hj]
  left_inv w := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [Function.update_self]
    · simp [Function.update_of_ne hj]
  right_inv w := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [Function.update_self]
    · simp [Function.update_of_ne hj]

theorem blockUpdate_apply (i : Fin fr.r)
    (B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i)) (w) :
    blockUpdate fr i B w = Function.update w i (B (w i)) := rfl

@[expose] abbrev blockCompl (i : Fin fr.r) : Type :=
  ∀ a : {j : Fin fr.r // j ≠ i}, Fin (fr.m a.1) → fr.E a.1

@[expose] noncomputable def blockRestrict (i : Fin fr.r)
    (B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i)) :
    (Fin (fr.m i) → fr.E i) ≃ₗ[F] (Fin (fr.m i) → fr.E i) :=
  (B : (Fin (fr.m i) → fr.E i) ≃ₗ[fr.E i] (Fin (fr.m i) → fr.E i)).restrictScalars F

@[expose] noncomputable def splitEquiv (i : Fin fr.r) :
    (∀ j, Fin (fr.m j) → fr.E j) ≃ₗ[F]
      (Fin (fr.m i) → fr.E i) × blockCompl fr i where
  toFun w := (w i, fun a => w a.1)
  invFun p := fun j => if h : j = i then h.symm ▸ p.1 else p.2 ⟨j, h⟩
  map_add' w w' := by
    ext <;> simp [Pi.add_apply]
  map_smul' c w := by
    ext <;> simp [Pi.smul_apply]
  left_inv w := by
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · show (if h : i = i then h.symm ▸ p.1 else p.2 ⟨i, h⟩) = p.1
      simp
    · funext a
      show (if h : a.1 = i then h.symm ▸ p.1 else p.2 ⟨a.1, h⟩) = p.2 a
      simp [a.2]

@[simp] private theorem splitEquiv_apply (i : Fin fr.r) (w) :
    splitEquiv fr i w = (w i, fun a : {j : Fin fr.r // j ≠ i} => w a.1) := rfl

@[simp] private theorem splitEquiv_symm_apply (i : Fin fr.r) (p) :
    (splitEquiv fr i).symm p =
      (fun j => if h : j = i then h.symm ▸ p.1 else p.2 ⟨j, h⟩) := rfl

theorem splitEquiv_blockUpdate (i : Fin fr.r)
    (B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i)) (w) :
    splitEquiv fr i (blockUpdate fr i B w) =
      (blockRestrict fr i B).prodCongr (LinearEquiv.refl F (blockCompl fr i))
        (splitEquiv fr i w) := by
  rw [splitEquiv_apply, LinearEquiv.prodCongr_apply, splitEquiv_apply]
  refine Prod.ext ?_ ?_
  · simp [blockUpdate_apply, Function.update_self]
    rfl
  · funext a
    simp [blockUpdate_apply, Function.update_of_ne a.2]

theorem det_blockRestrict (i : Fin fr.r)
    (B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i)) :
    LinearMap.det (blockRestrict fr i B :
      (Fin (fr.m i) → fr.E i) →ₗ[F] (Fin (fr.m i) → fr.E i)) = 1 := by
  rw [show (blockRestrict fr i B :
      (Fin (fr.m i) → fr.E i) →ₗ[F] (Fin (fr.m i) → fr.E i)) =
      ((B : (Fin (fr.m i) → fr.E i) →ₗ[fr.E i]
        (Fin (fr.m i) → fr.E i)).restrictScalars F) from rfl]
  rw [LinearMap.det_restrictScalars]
  have hB : LinearMap.det (B : (Fin (fr.m i) → fr.E i) →ₗ[fr.E i]
      (Fin (fr.m i) → fr.E i)) = 1 := by
    rw [← LinearEquiv.coe_det, B.prop]
    rfl
  rw [hB, map_one]

theorem blockUpdate_eq_conj (i : Fin fr.r)
    (B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i)) :
    blockUpdate fr i B =
      ((splitEquiv fr i).trans ((blockRestrict fr i B).prodCongr
        (LinearEquiv.refl F (blockCompl fr i)))).trans (splitEquiv fr i).symm := by
  apply LinearEquiv.ext
  intro w
  have h := congrArg (splitEquiv fr i).symm (splitEquiv_blockUpdate fr i B w)
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

theorem det_blockUpdate (i : Fin fr.r)
    (B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i)) :
    LinearEquiv.det (blockUpdate fr i B) = 1 := by
  have hP : LinearEquiv.det ((blockRestrict fr i B).prodCongr
      (LinearEquiv.refl F (blockCompl fr i))) = 1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det, LinearEquiv.coe_prodCongr, LinearMap.det_prodMap,
      det_blockRestrict]
    simp
  rw [blockUpdate_eq_conj]
  have h := LinearEquiv.det_conj (f := (blockRestrict fr i B).prodCongr
    (LinearEquiv.refl F (blockCompl fr i))) (e := (splitEquiv fr i).symm)
  rw [LinearEquiv.symm_symm] at h
  rw [h, hP]

theorem det_blockSpecialLinear (i : Fin fr.r)
    (B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i)) :
    LinearEquiv.det ((fr.Φ.trans (blockUpdate fr i B)).trans fr.Φ.symm) = 1 := by
  have h := LinearEquiv.det_conj (f := blockUpdate fr i B) (e := fr.Φ.symm)
  rw [LinearEquiv.symm_symm] at h
  rw [h, det_blockUpdate]

@[expose] noncomputable def blockSpecialLinear (i : Fin fr.r)
    (B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i)) : SpecialLinearGroup F V :=
  ⟨(fr.Φ.trans (blockUpdate fr i B)).trans fr.Φ.symm, det_blockSpecialLinear fr i B⟩

theorem blockSpecialLinear_apply (i : Fin fr.r)
    (B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i)) (v : V) :
    fr.Φ (blockSpecialLinear fr i B v) =
      Function.update (fr.Φ v) i (B (fr.Φ v i)) := by
  change fr.Φ (fr.Φ.symm (blockUpdate fr i B (fr.Φ v))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem blockSpecialLinear_mul (i : Fin fr.r)
    (B₁ B₂ : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i)) :
    blockSpecialLinear fr i (B₁ * B₂) =
      blockSpecialLinear fr i B₁ * blockSpecialLinear fr i B₂ := by
  apply SpecialLinearGroup.ext
  intro v
  apply fr.Φ.injective
  rw [blockSpecialLinear_apply fr i (B₁ * B₂) v]
  have hvv : (blockSpecialLinear fr i B₁ * blockSpecialLinear fr i B₂) v =
      blockSpecialLinear fr i B₁ (blockSpecialLinear fr i B₂ v) := by
    simp only [SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply]
  rw [hvv, blockSpecialLinear_apply fr i B₁ (blockSpecialLinear fr i B₂ v),
    blockSpecialLinear_apply fr i B₂ v, Function.update_self, Function.update_idem]
  simp only [SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply]

theorem exists_phi_eq (i : Fin fr.r) (x : Fin (fr.m i) → fr.E i) :
    ∃ v : V, fr.Φ v i = x := by
  refine ⟨fr.Φ.symm (Function.update (fun _ => 0) i x), ?_⟩
  rw [LinearEquiv.apply_symm_apply, Function.update_self]

theorem blockSpecialLinear_injective (i : Fin fr.r) :
    Function.Injective (blockSpecialLinear fr i) := by
  intro B₁ B₂ h
  ext x
  obtain ⟨v, hv⟩ := exists_phi_eq fr i x
  have h1 : B₁ x = fr.Φ (blockSpecialLinear fr i B₁ v) i := by
    rw [← hv, blockSpecialLinear_apply fr i B₁ v, Function.update_self]
  have h2 : B₂ x = fr.Φ (blockSpecialLinear fr i B₂ v) i := by
    rw [← hv, blockSpecialLinear_apply fr i B₂ v, Function.update_self]
  rw [h1, h2, h]

theorem blockUpdate_witness_unique (i : Fin fr.r) (g : SpecialLinearGroup F V)
    (B B' : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i))
    (hB : ∀ v, fr.Φ (g v) = Function.update (fr.Φ v) i (B (fr.Φ v i)))
    (hB' : ∀ v, fr.Φ (g v) = Function.update (fr.Φ v) i (B' (fr.Φ v i))) : B = B' := by
  ext x
  obtain ⟨v, hv⟩ := exists_phi_eq fr i x
  have h1 : B x = fr.Φ (g v) i := by rw [← hv, hB v, Function.update_self]
  have h2 : B' x = fr.Φ (g v) i := by rw [← hv, hB' v, Function.update_self]
  rw [h1, h2]

end SemiFrame

@[expose] def SemiFrame.slOnBlock (fr : SemiFrame F ρ) (i : Fin fr.r) :
    Subgroup (SpecialLinearGroup F V) where
  carrier := {g | ∃ B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i),
    ∀ v, fr.Φ (g v) = Function.update (fr.Φ v) i (B (fr.Φ v i))}
  mul_mem' := by
    rintro g₁ g₂ ⟨B₁, hB₁⟩ ⟨B₂, hB₂⟩
    refine ⟨B₁ * B₂, fun v => ?_⟩
    have hvv : (g₁ * g₂) v = g₁ (g₂ v) := by
      simp only [SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply]
    rw [hvv, hB₁ (g₂ v), hB₂ v, Function.update_self, Function.update_idem]
    simp only [SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply]
  one_mem' := by
    refine ⟨1, fun v => ?_⟩
    simp
  inv_mem' := by
    rintro g ⟨B, hB⟩
    refine ⟨B⁻¹, fun w => ?_⟩
    have h1 : g (g⁻¹ w) = w := by
      change ((g * g⁻¹ : SpecialLinearGroup F V) : V ≃ₗ[F] V) w = w
      rw [mul_inv_cancel, SpecialLinearGroup.coe_one]
      rfl
    have h := hB (g⁻¹ w)
    rw [h1] at h
    funext j
    by_cases hj : j = i
    · rw [hj, Function.update_self]
      have h2 : fr.Φ w i = B (fr.Φ (g⁻¹ w) i) := by
        have := congrFun h i
        simpa using this
      rw [h2]
      change fr.Φ (g⁻¹ w) i =
        ((B⁻¹ * B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i)) :
          (Fin (fr.m i) → fr.E i) ≃ₗ[fr.E i] (Fin (fr.m i) → fr.E i)) (fr.Φ (g⁻¹ w) i)
      rw [inv_mul_cancel, SpecialLinearGroup.coe_one]
      rfl
    · have h2 : fr.Φ w j = fr.Φ (g⁻¹ w) j := by
        have := congrFun h j
        simpa [Function.update_of_ne hj] using this
      rw [Function.update_of_ne hj]
      exact h2.symm


end CFSG.StandardType.StarFour
