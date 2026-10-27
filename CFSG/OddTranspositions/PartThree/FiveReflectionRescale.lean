module

public import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
public import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

private theorem two_ne_zero_zmod5 : (2 : ZMod 5) ≠ 0 := by decide

theorem isSquare_two_mul_iff {q : ZMod 5} (hq : q ≠ 0) :
    IsSquare (2 * q) ↔ ¬ IsSquare q := by
  have h : ∀ q : ZMod 5, q ≠ 0 → (IsSquare (2 * q) ↔ ¬ IsSquare q) := by decide
  exact h q hq

theorem isSquare_two_mul_iff_bool {π : Bool} {q : ZMod 5} (hq : q ≠ 0) :
    (IsSquare (2 * q) ↔ (!π) = true) ↔ (IsSquare q ↔ π = true) := by
  have h := isSquare_two_mul_iff hq
  cases π <;> simp [h]

section Field

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem conj_fiveReflOf_of_scale (n : ℕ) (ε ε' : Bool) (c : ZMod 5) (hc : c ≠ 0)
    (A : GL (Fin (n + 1)) (ZMod 5))
    (hA : ∀ x y, fiveForm n ε'
      ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x)
      ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ y) = c * fiveForm n ε x y)
    (v : Fin (n + 1) → ZMod 5) (hv : fiveForm n ε v v ≠ 0) :
    A * fiveReflOf n ε v * A⁻¹ =
      fiveReflOf n ε' ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ v) := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [fiveReflOf_mulVec]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hgy : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ
      (((A⁻¹ : GL (Fin (n + 1)) (ZMod 5)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ Pi.single i 1) = Pi.single i 1 := by
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  rw [hgy]
  rw [fiveReflOf_mulVec]
  have h1 : fiveForm n ε' (Pi.single i 1)
      ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ v) =
      c * fiveForm n ε
        (((A⁻¹ : GL (Fin (n + 1)) (ZMod 5)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ Pi.single i 1) v := by
    have := hA (((A⁻¹ : GL (Fin (n + 1)) (ZMod 5)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ Pi.single i 1) v
    rwa [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at this
  have h2 : fiveForm n ε' ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ v)
      ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ v) =
      c * fiveForm n ε v v := hA v v
  have hcoef : 2 * fiveForm n ε
        (((A⁻¹ : GL (Fin (n + 1)) (ZMod 5)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ Pi.single i 1) v *
        (fiveForm n ε v v)⁻¹ =
      2 * fiveForm n ε' (Pi.single i 1)
          ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ v) *
        (fiveForm n ε' ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ v)
          ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ v))⁻¹ := by
    rw [h1, h2]
    field_simp
  rw [hcoef]

private theorem conj_mem_fiveReflections_two {ε π : Bool} {A : GL (Fin 5) (ZMod 5)}
    (hA : ∀ x y, fiveForm 4 (!ε)
      ((A : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x)
      ((A : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ y) = 2 * fiveForm 4 ε x y)
    {r : GL (Fin 5) (ZMod 5)} (hr : r ∈ fiveReflections 4 ε π) :
    MulAut.conj A r ∈ fiveReflections 4 (!ε) (!π) := by
  obtain ⟨x, hx, hxπ, rfl⟩ := exists_eq_fiveReflOf hr
  rw [MulAut.conj_apply, conj_fiveReflOf_of_scale 4 ε (!ε) 2 two_ne_zero_zmod5 A hA x hx]
  refine fiveReflOf_mem ?_ ?_
  · rw [hA x x]
    exact mul_ne_zero two_ne_zero_zmod5 hx
  · rw [hA x x]
    exact (isSquare_two_mul_iff_bool hx).mpr hxπ

end Field

private noncomputable def quotientCenterMulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

@[simp] private theorem quotientCenterMulEquiv_mk {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (x : A) : quotientCenterMulEquiv e (QuotientGroup.mk x) = QuotientGroup.mk (e x) := by
  rw [quotientCenterMulEquiv, QuotientGroup.congr_mk]

theorem fischerCentralQuotientModel_of_subgroupEquiv {G : Type*} [Group G] {D : Set G}
    {ι F : Type*} [Fintype ι] [DecidableEq ι] [CommRing F]
    {H H' : Subgroup (GL ι F)} {T T' : Set (GL ι F)} (e : H ≃* H')
    (he : ∀ h : H, (h : GL ι F) ∈ T ↔ (e h : GL ι F) ∈ T')
    (h : CFSG.Open.fischerCentralQuotientModel D H T) :
    CFSG.Open.fischerCentralQuotientModel D H' T' := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.trans (quotientCenterMulEquiv e), fun g => ?_⟩
  rw [hφ g]
  constructor
  · rintro ⟨h, hh, hφg⟩
    refine ⟨e h, (he h).mp hh, ?_⟩
    rw [MulEquiv.trans_apply, hφg]
    exact quotientCenterMulEquiv_mk e h
  · rintro ⟨h', hh', hφg⟩
    have hq : quotientCenterMulEquiv e (φ g) = QuotientGroup.mk h' := by
      simpa only [MulEquiv.trans_apply] using hφg
    refine ⟨e.symm h', (he (e.symm h')).mpr (by simpa using hh'), ?_⟩
    apply (quotientCenterMulEquiv e).injective
    rw [hq, quotientCenterMulEquiv_mk, MulEquiv.apply_symm_apply]

private def rescaleVec (ε : Bool) (x : Fin 5 → ZMod 5) : Fin 5 → ZMod 5 :=
  ![x 0 + x 1, x 0 - x 1, x 2 + x 3, x 2 - x 3, (if ε then 1 else 2) * x 4]

private def rescaleMat (ε : Bool) : Matrix (Fin 5) (Fin 5) (ZMod 5) :=
  !![1, 1, 0, 0, 0;
     1, -1, 0, 0, 0;
     0, 0, 1, 1, 0;
     0, 0, 1, -1, 0;
     0, 0, 0, 0, (if ε then 1 else 2)]

private def rescaleMatInv (ε : Bool) : Matrix (Fin 5) (Fin 5) (ZMod 5) :=
  !![3, 3, 0, 0, 0;
     3, 2, 0, 0, 0;
     0, 0, 3, 3, 0;
     0, 0, 3, 2, 0;
     0, 0, 0, 0, (if ε then 1 else 3)]

private theorem rescaleMat_mul_inv (ε : Bool) :
    rescaleMat ε * rescaleMatInv ε = 1 := by
  cases ε <;> ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem rescaleMat_inv_mul (ε : Bool) :
    rescaleMatInv ε * rescaleMat ε = 1 := by
  cases ε <;> ext i j <;> fin_cases i <;> fin_cases j <;> decide

private def rescaleGL (ε : Bool) : GL (Fin 5) (ZMod 5) :=
  ⟨rescaleMat ε, rescaleMatInv ε, rescaleMat_mul_inv ε, rescaleMat_inv_mul ε⟩

@[simp] private theorem rescaleGL_val (ε : Bool) :
    (rescaleGL ε : Matrix (Fin 5) (Fin 5) (ZMod 5)) = rescaleMat ε := rfl

private theorem rescaleMat_mulVec (ε : Bool) (x : Fin 5 → ZMod 5) :
    (rescaleMat ε : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x = rescaleVec ε x := by
  ext i
  fin_cases i <;>
    simp [rescaleVec, Matrix.mulVec, dotProduct, Fin.sum_univ_five, rescaleMat] <;>
    ring_nf

private theorem rescale_form (ε : Bool) (x y : Fin 5 → ZMod 5) :
    fiveForm 4 (!ε)
      ((rescaleGL ε : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x)
      ((rescaleGL ε : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ y) =
      2 * fiveForm 4 ε x y := by
  rw [rescaleGL_val, rescaleMat_mulVec, rescaleMat_mulVec]
  cases ε <;> simp [rescaleVec, fiveForm, Fin.sum_univ_four] <;> ring_nf

private theorem image_conj_fiveReflections (ε π : Bool) :
    (MulAut.conj (rescaleGL ε)).toMonoidHom '' fiveReflections 4 ε π =
      fiveReflections 4 (!ε) (!π) := by
  ext g
  constructor
  · rintro ⟨r, hr, rfl⟩
    simpa using conj_mem_fiveReflections_two (rescale_form ε) hr
  · intro hg
    obtain ⟨y, hy, hyπ, rfl⟩ := exists_eq_fiveReflOf hg
    set x : Fin 5 → ZMod 5 :=
      (((rescaleGL ε)⁻¹ : GL (Fin 5) (ZMod 5)) :
        Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ y with hxdef
    have hAy : (rescaleGL ε : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x = y := by
      rw [hxdef, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    have hscale := rescale_form ε x x
    rw [hAy] at hscale
    have hxne : fiveForm 4 ε x x ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hscale
      exact hy hscale
    refine ⟨fiveReflOf 4 ε x, ?_, ?_⟩
    · refine fiveReflOf_mem hxne ?_
      rw [← isSquare_two_mul_iff_bool hxne, ← hscale]
      exact hyπ
    · change MulAut.conj (rescaleGL ε) (fiveReflOf 4 ε x) = fiveReflOf 4 (!ε) y
      rw [MulAut.conj_apply,
        conj_fiveReflOf_of_scale 4 ε (!ε) 2 two_ne_zero_zmod5 (rescaleGL ε) (rescale_form ε)
          x hxne, hAy]

private theorem map_conj_fiveReflectionGroup (ε π : Bool) :
    (fiveReflectionGroup 4 ε π).map (MulAut.conj (rescaleGL ε)).toMonoidHom =
      fiveReflectionGroup 4 (!ε) (!π) := by
  unfold fiveReflectionGroup
  rw [MonoidHom.map_closure, image_conj_fiveReflections]

private noncomputable abbrev conjSubgroupEquiv (ε π : Bool) :
    fiveReflectionGroup 4 ε π ≃* fiveReflectionGroup 4 (!ε) (!π) :=
  (MulEquiv.subgroupMap (MulAut.conj (rescaleGL ε)) (fiveReflectionGroup 4 ε π)).trans
    (MulEquiv.subgroupCongr (map_conj_fiveReflectionGroup ε π))

@[simp] private theorem conjSubgroupEquiv_apply (ε π : Bool)
    (h : fiveReflectionGroup 4 ε π) :
    (conjSubgroupEquiv ε π h : GL (Fin 5) (ZMod 5)) = MulAut.conj (rescaleGL ε) h := rfl

private theorem conjSubgroupEquiv_mem (ε π : Bool) (h : fiveReflectionGroup 4 ε π) :
    (h : GL (Fin 5) (ZMod 5)) ∈ fiveReflections 4 ε π ↔
      (conjSubgroupEquiv ε π h : GL (Fin 5) (ZMod 5)) ∈ fiveReflections 4 (!ε) (!π) := by
  rw [conjSubgroupEquiv_apply]
  constructor
  · intro hh
    rw [← image_conj_fiveReflections]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← image_conj_fiveReflections] at hh
    obtain ⟨r, hr, hr'⟩ := hh
    have : r = h := (MulAut.conj (rescaleGL ε)).injective hr'
    rwa [← this]

theorem IsFiveReflectionModel.four_not {X : Type} [Group X] {Θ : Set X} {ε π : Bool}
    (h : IsFiveReflectionModel 4 ε π Θ) : IsFiveReflectionModel 4 (!ε) (!π) Θ :=
  fischerCentralQuotientModel_of_subgroupEquiv (conjSubgroupEquiv ε π)
    (conjSubgroupEquiv_mem ε π) h

end CFSG.OddTranspositions.PartThree

end
